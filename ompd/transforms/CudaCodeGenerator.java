package ompd.transforms;

import cetus.analysis.LoopTools;
import cetus.exec.Driver;
import cetus.hir.*;
import cetus.transforms.TransformPass;
import ompd.hir.*;

import java.util.*;

public class CudaCodeGenerator extends AccCodeGenerator
{
    private static final String CUDA_PREFIX = "gpu__";
    private static final String CUDA_THREAD_ID_X = "threadIdx.x";
    private static final String CUDA_BLOCK_ID_X = "blockIdx.x";
    private static final String CUDA_BLOCK_ID_Y = "blockIdx.y";
    private static final String CUDA_BLOCK_DIM_X = "blockDim.x";
    private static final String CUDA_GRID_DIM_X = "gridDim.x";

    private static final String CUDA_SYNCTHREADS = "__syncthreads";

    private static final List<Specifier> returnSpec = Arrays.asList(CudaSpecifier.CUDA_GLOBAL, Specifier.VOID);

    public CudaCodeGenerator(Program prog)
    {
        super(prog);
    }

    @Override
    protected void insertHeader()
    {
        String header_code = "#include \"ompc.h\"";
        CodeAnnotation code_annot = new CodeAnnotation(header_code);
        AnnotationDeclaration anote = new AnnotationDeclaration(code_annot);

        // TODO: Do refactoring
        BreadthFirstIterator bfs_iter = new BreadthFirstIterator(program);
        bfs_iter.pruneOn(TranslationUnit.class);

        for (; ; )
        {
            TranslationUnit tu = null;
            try
            {
                tu = (TranslationUnit) bfs_iter.next(TranslationUnit.class);
                tu.addDeclarationFirst(anote);
            }
            catch (NoSuchElementException e)
            {
                return;
            }
        }
    }

    @Override
    public String getPassName()
    {
        return "[CudaCodeGenerator]";
    }

    @Override
    protected AccMemoryAllocation generateAccMemoryAllocation(OmpdAnnotation annot, HashMap<Symbol, AccMemoryAllocation> accVarMap)
    {
        Statement curStmt = (Statement)annot.getAnnotatable();
        CompoundStatement parentStmt = (CompoundStatement) curStmt.getParent();

        Symbol cpuVar = (Symbol)annot.get(OmpdAnnotation.ACC_DATA_CREATE);

        /* Create GPU variable */
        String gpuVarName = CUDA_PREFIX + cpuVar.getSymbolName() + Integer.toString(accVarCount);
        PrintTools.println("Create GPU variable " + gpuVarName, 0);
        VariableDeclarator gpuVarDeclarator = new VariableDeclarator(new NameID(gpuVarName));
        List<Specifier> gpuVarSpecifier = new ArrayList<Specifier>();

        gpuVarSpecifier.addAll(cpuVar.getTypeSpecifiers());
        if(SymbolTools.isArray(cpuVar))
        {
            gpuVarSpecifier.add(PointerSpecifier.UNQUALIFIED);
        }

        Declaration gpuVarDeclaration = new VariableDeclaration(gpuVarSpecifier ,gpuVarDeclarator);
        DeclarationStatement gpuVarDeclarationStmt = new DeclarationStatement(gpuVarDeclaration);

        parentStmt.addStatementAfter(curStmt, gpuVarDeclarationStmt);
        SymbolTools.addSymbols(parentStmt, gpuVarDeclaration);
        Symbol gpuVar = SymbolTools.getSymbolOfName(gpuVarName, parentStmt);
        /* End Create GPU variable */

        AccMemoryAllocation accMemAlloc = new CudaMemoryAllocation(cpuVar, gpuVar,
                (Integer)annot.get(OmpdAnnotation.ACC_DATA_DIMENSION),
                (List<Expression>)annot.get(OmpdAnnotation.ACC_DATA_SIZE),
                (List<Expression>)annot.get(OmpdAnnotation.ACC_DATA_OFFSET),
                CudaMemoryAllocation.AllocationType.CUDA_MALLOC);

        Statement memAllocStmt = accMemAlloc.generateMemoryAllocationCode(parentStmt, gpuVarDeclarationStmt);

        FunctionCall accRtRegisterCall = new FunctionCall(new NameID(OMPD_ACC_RT_REGISTER));
        accRtRegisterCall.addArgument(new Typecast(Arrays.asList(Specifier.VOID, PointerSpecifier.UNQUALIFIED), new Identifier(cpuVar)));
        accRtRegisterCall.addArgument(new Typecast(Arrays.asList(Specifier.VOID, PointerSpecifier.UNQUALIFIED), new Identifier(gpuVar)));
        accRtRegisterCall.addArgument(new IntegerLiteral((Integer) annot.get(OmpdAnnotation.ACC_DATA_DIMENSION)));
        for(Expression offset : (List<Expression>)annot.get(OmpdAnnotation.ACC_DATA_OFFSET))
        {
            accRtRegisterCall.addArgument(offset.clone());
        }

        OMPDTools.convertToOmpdProcId(accRtRegisterCall);
        parentStmt.addStatementAfter(memAllocStmt, new ExpressionStatement(accRtRegisterCall));


        return accMemAlloc;
    }

    @Override
    protected AccMemoryTransfer generateAccMemoryTransfer(OmpdAnnotation annot, AccMemoryAllocation accMemAllocation, AccMemoryTransfer.TransferDirection direction)
    {
        return  new CudaMemoryTransfer(
                accMemAllocation,
                (List<Expression>)annot.get(OmpdAnnotation.ACC_DATA_POSITION),
                (List<Expression>)annot.get(OmpdAnnotation.ACC_DATA_SIZE),
                direction);
    }

    @Override
    protected AccMemoryFree generateAccMemoryDeallocation(AccMemoryAllocation accMemAllocation)
    {
        return new CudaMemoryFree(accMemAllocation);
    }

    @Override
    protected void generateAccKernel(Procedure proc,OmpdAnnotation annot, CompoundStatement parentStmt, Statement curStmt, Map<Symbol, AccMemoryAllocation> accVarMap)
    {
        String kernelName = (String)annot.get(OmpdAnnotation.ACC_KERNEL);

        List<Declaration> parameterList = new ArrayList<Declaration>();
        List<Expression>  argumentList = new ArrayList<Expression>();

        Statement kernelStatement = (Statement)annot.getAnnotatable();
        kernelStatement = kernelStatement.clone();
        kernelStatement.removeAnnotations();

        CompoundStatement kernelBody = new CompoundStatement();
        kernelBody.addStatement(kernelStatement);

        HashSet<VariableDeclarator> sharedVariables = (HashSet<VariableDeclarator>)annot.get("shared");
        HashSet<VariableDeclarator> privateVariables = (HashSet<VariableDeclarator>)annot.get("private");
        HashSet<VariableDeclarator> ompdVariables = collectOmpdVariables(kernelBody, sharedVariables, privateVariables);

        Expression cudaGridSizeX = new IntegerLiteral(1);
        Expression cudaGridSizeY = new IntegerLiteral(1);
        Expression cudaGridSizeZ = new IntegerLiteral(1);

        int cudaThreadBlockSizeX = Integer.parseInt(Driver.getOptionValue("cuda-thread-block-size-x"));
        int cudaThreadBlockSizeY = 1;
        int cudaThreadBlockSizeZ = 1;

        /**
         *  Collect shared variables to make function parameters and
         *  function call arguments.
         */
        for(Symbol var : sharedVariables)
        {
            if(accVarMap.containsKey(var))
            {
                PrintTools.println("Found shared variable " + var.getSymbolName(), 0);
                AccMemoryAllocation accMemoryAllocation = accVarMap.get(var);
                Symbol gpuVar = accMemoryAllocation.getAccSymbol();

                VariableDeclarator paramDeclarator = new VariableDeclarator(new Identifier(var));
                parameterList.add(new VariableDeclaration(gpuVar.getTypeSpecifiers(), paramDeclarator));

                argumentList.add(new Identifier(gpuVar));
            }
            else if(!SymbolTools.isArray(var))
            {
                // Assume that the var is read-only variable
                // TODO: Check if the var is read-only or not

                PrintTools.println("Found pass by value variable " + var.getSymbolName(), 0);
                VariableDeclarator paramDeclarator = new VariableDeclarator(new Identifier(var));
                parameterList.add(new VariableDeclaration(var.getTypeSpecifiers(), paramDeclarator));

                argumentList.add(new Identifier(var));
            }
            else
            {
                throw new RuntimeException("Shared array is not allocated on accelerator: " + var.getSymbolName());
            }
        }

        /**
         *  Collect OMPD specific variables to make function parameters and
         *  function call arguments.
         */
        for(Symbol var : ompdVariables)
        {
            //TODO: BUG. This code add ompd_lb[ompd_procid] as input value for both ompd_lb and ompd_ub parameters
            VariableDeclarator paramDeclarator = new VariableDeclarator(new Identifier(var));
            parameterList.add(new VariableDeclaration(var.getTypeSpecifiers(), paramDeclarator));

            Iterator iterator = new DepthFirstIterator(kernelBody);
            while (iterator.hasNext())
            {
                Object o = iterator.next();
                if(o instanceof ArrayAccess)
                {
                    ArrayAccess access = (ArrayAccess)o;
                    Identifier arrayId = (Identifier)access.getArrayName();

                    if(ompdVariables.contains(arrayId.getSymbol()))
                    {
                        //IRTools.replaceAll(access.getParent(),access, new Identifier(arrayId.getSymbol()));
                        argumentList.add(access);
                        break;
                    }
                }
            }
        }

        if(kernelStatement instanceof ForLoop)
        {
            ForLoop kernelLoop = (ForLoop)kernelStatement;

            /**
             * Declare CUDA specific variable blockId and threadId
             * Assume that 1D partitioning is used
             *
             * __blockId = blockIdx.x+(blockIdx.y*gridDim.x)
             * __threadId = (threadIdx.x+(_blockId*blockDim.x));
             *
             * TODO: Support multidimensional partitioning
             */
            VariableDeclarator blockIdDeclarator = new VariableDeclarator(new NameID("__blockId"));
            Expression blockIdExp = Symbolic.multiply(new NameID(CUDA_BLOCK_ID_Y), new NameID(CUDA_GRID_DIM_X));
            blockIdExp = Symbolic.add(new NameID(CUDA_BLOCK_ID_X), blockIdExp);
            blockIdDeclarator.setInitializer(new Initializer(blockIdExp));
            VariableDeclaration blockDecl = new VariableDeclaration(Specifier.INT ,blockIdDeclarator);
            // If this declaration is the first declaration
            if(kernelBody.getDeclarations().size() == 0)
            {
                kernelBody.addDeclaration(blockDecl);
            }
            else
            {
                Declaration firstDecl = null;
                for (Traversable child : kernelBody.getChildren())
                {
                    if (child instanceof DeclarationStatement)
                    {
                        DeclarationStatement declStmt = (DeclarationStatement) child;
                        firstDecl = declStmt.getDeclaration();
                        break;
                    }
                }
                kernelBody.addDeclarationBefore(firstDecl, blockDecl);
            }

            VariableDeclarator threadIdDeclarator = new VariableDeclarator(new NameID("__threadId"));
            Expression threadIdExp = Symbolic.multiply(blockIdDeclarator.getID(), new NameID(CUDA_BLOCK_DIM_X));
            threadIdExp = Symbolic.add(new NameID(CUDA_THREAD_ID_X), threadIdExp);
            threadIdDeclarator.setInitializer(new Initializer(threadIdExp));
            kernelBody.addDeclarationAfter(blockDecl, new VariableDeclaration(Specifier.INT ,threadIdDeclarator));

            /**
             * Declare loop variable
             */
            List<Expression> indexVarList = LoopTools.collectIndexVariables(kernelLoop);
            for(Expression var : indexVarList)
            {
                Identifier indexVar = (Identifier)var;

                VariableDeclaration indexDeclaration = (VariableDeclaration)SymbolTools.findSymbol(kernelBody, indexVar.getName());

                if(indexDeclaration == null)
                {
                    VariableDeclarator indexDeclarator = new VariableDeclarator(indexVar);
                    kernelBody.addDeclaration(new VariableDeclaration(indexVar.getSymbol().getTypeSpecifiers(),
                            indexDeclarator));
                }
            }

            ForLoop targetLoop;
            List<ForLoop> loops = LoopTools.collectForLoops(kernelLoop);

            /**
             * If loop is perfectly nested, convert innermost loop to use thread id instead of loop index
             * else convert outermost loop to use thread id instead of loop index
             */
            if(LoopTools.isPerfectNest(kernelLoop))
            {
                targetLoop = loops.get(loops.size()-1);
            }
            else
            {
                targetLoop = loops.get(0);
            }

            Expression lowerBoundExpression = LoopTools.getLowerBoundExpression(targetLoop);
            Expression upperBoundExpression = LoopTools.getUpperBoundExpression(targetLoop);

            Symbol targetLoopIndexSymbol = LoopTools.getLoopIndexSymbol(targetLoop);
            VariableDeclaration targetLoopVarDeclaration = (VariableDeclaration)SymbolTools.findSymbol(kernelBody, targetLoopIndexSymbol.getSymbolName());
            VariableDeclarator targetLoopVarDeclarator = (VariableDeclarator)targetLoopVarDeclaration.getDeclarator(0);

            Initializer initializer = new Initializer(Symbolic.add(threadIdDeclarator.getID(),lowerBoundExpression));
            targetLoopVarDeclarator.setInitializer(initializer);

            /**
             * Add condition for upperbound
             */
            Expression condition = targetLoop.getCondition().clone();
            IfStatement upperCondition = new IfStatement(Symbolic.negate(condition), new ReturnStatement());
            kernelBody.addStatementBefore(kernelLoop, upperCondition);

            /**
             * Remove inner loop
             */
            CompoundStatement innermostLoopParent = (CompoundStatement) targetLoop.getParent();
            innermostLoopParent.addStatementAfter(targetLoop, targetLoop.getBody().clone());
            innermostLoopParent.removeChild(targetLoop);

            /**
             * Compute the size of CUDA grid
             * TODO: Support multidimensional partitioning
             * TODO: Add heuristic algorithm to determine block and grid size
             *       based on device parameter e.g. number of SM, shared memory size
             */
            Expression innerLoopIterationCount = Symbolic.add(Symbolic.subtract(upperBoundExpression, lowerBoundExpression), new IntegerLiteral(1));

            cudaGridSizeX = Symbolic.add(Symbolic.divide(innerLoopIterationCount, new IntegerLiteral(cudaThreadBlockSizeX)), new IntegerLiteral(1));
        }
        else
        {
            throw new RuntimeException("Current Implementation support only For Loop");
        }

        /**
         *  Collect private variables and declare them inside the kernel
         */
        for(VariableDeclarator var : privateVariables)
        {
            PrintTools.println("Private: '" + var.getID() + "'", 0);

            VariableDeclaration privateDeclaration = (VariableDeclaration)SymbolTools.findSymbol(kernelBody, var.getSymbolName());
            if(privateDeclaration != null)
                continue;

            Traversable t = var.getParent();
            VariableDeclaration privateSymbol = null;

            while(t != null)
            {
                if(t instanceof SymbolTable)
                {
                    privateSymbol = (VariableDeclaration)SymbolTools.findSymbol((SymbolTable)t, var.getID());
                    break;
                }
                t = t.getParent();
            }

            PrintTools.println( "" + privateSymbol, 0);

            VariableDeclaration decl = new VariableDeclaration(privateSymbol.getSpecifiers(), var);
            kernelBody.addDeclaration(decl);
        }


        offsetArrayAccess(kernelBody, accVarMap);
        convertOmpdVariable(kernelBody);
        generateAccArrayAccess(kernelBody, accVarMap);

        /**
         *  Create kernel function declaration
         */
        Declarator accFunctionDeclarator = new ProcedureDeclarator(new NameID(kernelName), new LinkedList());

        for(Declaration param : parameterList)
        {
            accFunctionDeclarator.addParameter(param);
        }

        Procedure accFunction = new Procedure(returnSpec, accFunctionDeclarator, kernelBody);

        TranslationUnit translationUnit = (TranslationUnit)proc.getParent();
        translationUnit.addDeclarationBefore(proc, accFunction);

        /**
         * Create gridBlock size
         * TODO: Add support for multidimensional partitioning
         */
        CudaDim3Specifier dim3GridSpec = new CudaDim3Specifier(cudaGridSizeX, cudaGridSizeY, cudaGridSizeZ);
        VariableDeclarator dimGridDeclarator = new VariableDeclarator(new NameID("dimGrid_"+kernelName), dim3GridSpec);
        Identifier dimGrid = new Identifier(dimGridDeclarator);
        Declaration dimGridDeclaration = new VariableDeclaration(CudaSpecifier.CUDA_DIM3, dimGridDeclarator);
        parentStmt.addStatementBefore(curStmt, new DeclarationStatement(dimGridDeclaration));

        /**
         * Create threadBlock size
         * TODO: Add support for multidimensional partitioning
         */
        CudaDim3Specifier dim3BlockSpec = new CudaDim3Specifier(new IntegerLiteral(cudaThreadBlockSizeX), new IntegerLiteral(1),new IntegerLiteral(1));
        VariableDeclarator dimBlockDeclarator = new VariableDeclarator(new NameID("dimBlock_"+kernelName), dim3BlockSpec);
        Identifier dimBlock = new Identifier(dimBlockDeclarator);
        Declaration dimBlockDeclaration = new VariableDeclaration(CudaSpecifier.CUDA_DIM3, dimBlockDeclarator);
        parentStmt.addStatementBefore(curStmt, new DeclarationStatement(dimBlockDeclaration));

        /**
         * Create kernel function call
         */
        CudaKernelCall kernelCall = new CudaKernelCall(new NameID(kernelName), new ArrayList());

        for(Expression arg : argumentList)
        {
            kernelCall.addArgument(arg.clone());
        }

        kernelCall.setGridSize(dimGrid);
        kernelCall.setBlockSize(dimBlock);

        OMPDTools.convertToOmpdProcId(kernelCall);

        parentStmt.addStatementAfter(curStmt, new ExpressionStatement(kernelCall));

        /**
         * Remove parallel loop
         */
        parentStmt.removeStatement(curStmt);
    }

    @Override
    protected void generateAccReductionKernel(Procedure proc,OmpdAnnotation annot, CompoundStatement parentStmt, Statement curStmt, Map<Symbol, AccMemoryAllocation> accVarMap)
    {
        String kernelName = (String)annot.get(OmpdAnnotation.ACC_KERNEL);

        List<Declaration> parameterList = new ArrayList<Declaration>();
        List<Expression>  argumentList = new ArrayList<Expression>();

        Statement kernelStatement = (Statement)annot.getAnnotatable();
        kernelStatement = kernelStatement.clone();
        kernelStatement.removeAnnotations();

        CompoundStatement kernelBody = new CompoundStatement();
        kernelBody.addStatement(kernelStatement);

        HashSet<VariableDeclarator> sharedVariables = (HashSet<VariableDeclarator>)annot.get("shared");
        HashSet<VariableDeclarator> privateVariables = (HashSet<VariableDeclarator>)annot.get("private");
        HashSet<VariableDeclarator> ompdVariables = collectOmpdVariables(kernelBody, sharedVariables, privateVariables);
        HashMap<String, HashSet<String>> reductionVariables = annot.get("reduction");

        Expression cudaGridSizeX = new IntegerLiteral(1);
        Expression cudaGridSizeY = new IntegerLiteral(1);
        Expression cudaGridSizeZ = new IntegerLiteral(1);

        int cudaThreadBlockSizeX = Integer.parseInt(Driver.getOptionValue("cuda-thread-block-size-x"));
        int cudaThreadBlockSizeY = 1;
        int cudaThreadBlockSizeZ = 1;

        /**
         *  Collect shared variables to make function parameters and
         *  function call arguments.
         */
        for(Symbol var : sharedVariables)
        {
            if(accVarMap.containsKey(var))
            {
                PrintTools.println("Found shared variable " + var.getSymbolName(), 0);
                AccMemoryAllocation accMemoryAllocation = accVarMap.get(var);
                Symbol gpuVar = accMemoryAllocation.getAccSymbol();

                VariableDeclarator paramDeclarator = new VariableDeclarator(new Identifier(var));
                parameterList.add(new VariableDeclaration(gpuVar.getTypeSpecifiers(), paramDeclarator));

                argumentList.add(new Identifier(gpuVar));
            }
            else if(!SymbolTools.isArray(var))
            {
                // Assume that the var is read-only variable
                // TODO: Check if the var is read-only or not

                PrintTools.println("Found pass by value variable " + var.getSymbolName(), 0);
                VariableDeclarator paramDeclarator = new VariableDeclarator(new Identifier(var));
                parameterList.add(new VariableDeclaration(var.getTypeSpecifiers(), paramDeclarator));

                argumentList.add(new Identifier(var));
            }
            else
            {
                throw new RuntimeException("Shared array is not allocated on accelerator: " + var.getSymbolName());
            }
        }

        /**
         *  Collect OMPD specific variables to make function parameters and
         *  function call arguments.
         */
        for(Symbol var : ompdVariables)
        {
            VariableDeclarator paramDeclarator = new VariableDeclarator(new Identifier(var));
            parameterList.add(new VariableDeclaration(var.getTypeSpecifiers(), paramDeclarator));

            Iterator iterator = new DepthFirstIterator(kernelBody);
            while (iterator.hasNext())
            {
                Object o = iterator.next();
                if(o instanceof ArrayAccess)
                {
                    ArrayAccess access = (ArrayAccess)o;
                    Identifier arrayId = (Identifier)access.getArrayName();

                    if(ompdVariables.contains(arrayId.getSymbol()))
                    {
                        IRTools.replaceAll(access.getParent(),access, new Identifier(arrayId.getSymbol()));
                        argumentList.add(access);
                        break;
                    }
                }
            }
        }

        /**
         *  Collect reduction variables to make function parameters and
         *  function call arguments.
         */
        for(String reductionOp:reductionVariables.keySet())
        {
            for(String reductionVar: reductionVariables.get(reductionOp))
            {
                String gpuRedVarName = CUDA_PREFIX + reductionVar;

                Set<Symbol> tables = proc.getSymbols();
                Symbol redVarSymbol = SymbolTools.getSymbolOfName(reductionVar, ((Statement) annot.getAnnotatable()).getParent());
                List<Specifier> globalRedVarSpecList = new ArrayList<Specifier>();
                VariableDeclaration redVarDeclaration = (VariableDeclaration)redVarSymbol.getDeclaration();
                globalRedVarSpecList.addAll(redVarDeclaration.getSpecifiers());
                globalRedVarSpecList.add(PointerSpecifier.UNQUALIFIED);

                VariableDeclarator paramDeclarator = new VariableDeclarator(new NameID(gpuRedVarName));
                parameterList.add(new VariableDeclaration(globalRedVarSpecList, paramDeclarator));
            }
        }

        offsetArrayAccess(kernelBody, accVarMap);
        convertOmpdVariable(kernelBody);
        generateAccArrayAccess(kernelBody, accVarMap);

        /**
         * Create kernel body
         */
        if(kernelStatement instanceof ForLoop)
        {
            ForLoop kernelLoop = (ForLoop)kernelStatement;

            /**
             * Declare CUDA specific variable blockId and threadId
             * Assume that 1D partitioning is used
             *
             * __blockId = blockIdx.x+(blockIdx.y*gridDim.x)
             * __threadId = (threadIdx.x+(_blockId*blockDim.x));
             *
             * TODO: Support multidimensional partitioning
             */
            VariableDeclarator blockIdDeclarator = new VariableDeclarator(new NameID("__blockId"));
            Expression blockIdExp = Symbolic.multiply(new NameID(CUDA_BLOCK_ID_Y), new NameID(CUDA_GRID_DIM_X));
            blockIdExp = Symbolic.add(new NameID(CUDA_BLOCK_ID_X), blockIdExp);
            blockIdDeclarator.setInitializer(new Initializer(blockIdExp));
            kernelBody.addDeclaration(new VariableDeclaration(Specifier.INT ,blockIdDeclarator));

            VariableDeclarator threadIdDeclarator = new VariableDeclarator(new NameID("__threadId"));
            Expression threadIdExp = Symbolic.multiply(blockIdDeclarator.getID(), new NameID(CUDA_BLOCK_DIM_X));
            threadIdExp = Symbolic.add(new NameID(CUDA_THREAD_ID_X), threadIdExp);
            threadIdDeclarator.setInitializer(new Initializer(threadIdExp));
            kernelBody.addDeclaration(new VariableDeclaration(Specifier.INT ,threadIdDeclarator));

            /**
             * Declare reduction variable
             */
            for(String reductionOp:reductionVariables.keySet())
            {
                for(String reductionVar: reductionVariables.get(reductionOp))
                {
                    Set<Symbol> tables = proc.getSymbols();
                    Symbol redVarSymbol = SymbolTools.getSymbolOfName(reductionVar, ((Statement) annot.getAnnotatable()).getParent());
                    List<Specifier> redVarSpecList = new ArrayList<Specifier>();
                    redVarSpecList.add(CudaSpecifier.CUDA_SHARED);
                    VariableDeclaration redVarDeclaration = (VariableDeclaration)redVarSymbol.getDeclaration();
                    redVarSpecList.addAll(redVarDeclaration.getSpecifiers());
                    ArraySpecifier redVarSize = new ArraySpecifier(new IntegerLiteral(cudaThreadBlockSizeX));

                    String redVarName = "__shared_"+reductionVar;

                    VariableDeclarator redVarDeclarator = new VariableDeclarator(new NameID(redVarName), redVarSize);
                    kernelBody.addDeclaration(new VariableDeclaration(redVarSpecList ,redVarDeclarator));

                    /**
                     * Init value of the reduction varible in shared memory based on operator type
                     */
                    AssignmentExpression redInitAssignment = null;
                    if(reductionOp.compareTo("+") == 0 || reductionOp.compareTo("-") == 0)
                    {
                        redInitAssignment = new AssignmentExpression(new ArrayAccess(new NameID(redVarName), new NameID(CUDA_THREAD_ID_X)) ,
                                                                                   AssignmentOperator.NORMAL,
                                                                                   new IntegerLiteral(0));
                    }
                    else
                    {
                        throw new RuntimeException("Reduction operator : " + reductionOp + " is not supported");
                    }
                    kernelBody.addStatementBefore(kernelLoop, new ExpressionStatement(redInitAssignment));

                    /**
                     * Replace all reduction variable with shared memory
                     */
                    IRTools.replaceAll(kernelBody, new NameID(reductionVar), new ArrayAccess(new NameID(redVarName), new NameID(CUDA_THREAD_ID_X)));
                }
            }

            /**
             * Compute the reduction
             */
            // Call __syncthreads()
            FunctionCall syncThreadsCall = new FunctionCall(new NameID(CUDA_SYNCTHREADS));
            ExpressionStatement syncThreadsStmt = new ExpressionStatement(syncThreadsCall);
            kernelBody.addStatementAfter(kernelLoop, syncThreadsStmt);

            // Declare iterator for reduction named __red_i_0, __red_i_1, and __red_i_2
            List<Specifier> redIterSpecList = new ArrayList<Specifier>();
            redIterSpecList.add(Specifier.INT);
            VariableDeclarator redIterDecl = new VariableDeclarator(new NameID("__red_i_0"));
            redIterDecl.setInitializer(new Initializer(new IntegerLiteral(cudaThreadBlockSizeX)));
            VariableDeclaration redIterDeclaration = new VariableDeclaration(redIterSpecList,redIterDecl);
            kernelBody.addDeclaration(redIterDeclaration);

            redIterSpecList = new ArrayList<Specifier>();
            redIterSpecList.add(Specifier.INT);
            redIterDecl = new VariableDeclarator(new NameID("__red_i_1"));
            redIterDecl.setInitializer(new Initializer(new IntegerLiteral(cudaThreadBlockSizeX)));
            redIterDeclaration = new VariableDeclaration(redIterSpecList,redIterDecl);
            kernelBody.addDeclaration(redIterDeclaration);

            /**
             * Create Reduction loop
             */

            // Create reduction loop body
            AssignmentExpression reductionLoopInit = new AssignmentExpression(
                    new NameID("__red_i_0"),
                    AssignmentOperator.NORMAL,
                    new BinaryExpression(new IntegerLiteral(cudaThreadBlockSizeX), BinaryOperator.SHIFT_RIGHT, new IntegerLiteral(1))
            );

            ForLoop reductionLoop = new ForLoop(
                    new ExpressionStatement(reductionLoopInit),
                    new BinaryExpression(new NameID("__red_i_0"), BinaryOperator.COMPARE_GT, new IntegerLiteral(0)),
                    new AssignmentExpression(new NameID("__red_i_0"),AssignmentOperator.SHIFT_RIGHT, new IntegerLiteral(1)),
                    new CompoundStatement()
            );

            CompoundStatement reductionLoopBody = (CompoundStatement)reductionLoop.getBody();

            //Condition for reduction
            IfStatement reductionCondition = new IfStatement(
                    new BinaryExpression(new NameID(CUDA_THREAD_ID_X), BinaryOperator.COMPARE_LT, new NameID("__red_i_0")),
                    new CompoundStatement()
            );

            //Create reduction computation body
            CompoundStatement reductionBody = (CompoundStatement)reductionCondition.getThenStatement();
            for(String reductionOp:reductionVariables.keySet())
            {
                for(String reductionVar: reductionVariables.get(reductionOp))
                {
                    String redVarName = "__shared_"+reductionVar;
                    if(reductionOp.compareTo("+") == 0)
                    {
                        reductionBody.addStatement(
                                new ExpressionStatement(new AssignmentExpression(
                                        new ArrayAccess(new NameID(redVarName), new NameID(CUDA_THREAD_ID_X)),
                                        AssignmentOperator.ADD,
                                        new ArrayAccess(new NameID(redVarName), new BinaryExpression(
                                                new NameID(CUDA_THREAD_ID_X), BinaryOperator.ADD, new NameID("__red_i_0"))
                                        )
                                ))
                        );
                    }
                }
            }
            reductionLoopBody.addStatement(reductionCondition);

            //If the size is not divisible by 2 and threadId.x == 0
            IfStatement reductionNotDivisibleCondition = new IfStatement(
                    new BinaryExpression(
                        new BinaryExpression(
                                new BinaryExpression(new NameID("__red_i_1"), BinaryOperator.BITWISE_AND, new IntegerLiteral(1)),
                                BinaryOperator.COMPARE_EQ,
                                new IntegerLiteral(1)),
                        BinaryOperator.LOGICAL_AND,
                        new BinaryExpression(new NameID(CUDA_THREAD_ID_X), BinaryOperator.COMPARE_EQ, new IntegerLiteral(0))),
                    new CompoundStatement()
            );

            CompoundStatement reductionNotDivisibleBody = (CompoundStatement)reductionNotDivisibleCondition.getThenStatement();
            for(String reductionOp:reductionVariables.keySet())
            {
                for(String reductionVar: reductionVariables.get(reductionOp))
                {
                    String redVarName = "__shared_"+reductionVar;
                    if(reductionOp.compareTo("+") == 0)
                    {
                        reductionNotDivisibleBody.addStatement(
                                new ExpressionStatement(new AssignmentExpression(
                                        new ArrayAccess(new NameID(redVarName), new IntegerLiteral(0)),
                                        AssignmentOperator.ADD,
                                        new ArrayAccess(new NameID(redVarName), new BinaryExpression(
                                                new NameID("__red_i_1"), BinaryOperator.SUBTRACT, new IntegerLiteral(1))
                                        )
                                ))
                        );
                    }
                }
            }
            reductionLoopBody.addStatementAfter(reductionCondition, reductionNotDivisibleCondition);

            //Update __red_i_1 value to __red_i_0 value
            ExpressionStatement reductionIteratorUpdateStmt = new ExpressionStatement(
                    new AssignmentExpression(new NameID("__red_i_1"),AssignmentOperator.NORMAL, new NameID("__red_i_0")));
            reductionLoopBody.addStatementAfter(reductionNotDivisibleCondition,reductionIteratorUpdateStmt);

            // Call __syncthreads()
            ExpressionStatement syncThreadsStmt2 = syncThreadsStmt.clone();
            reductionLoopBody.addStatementAfter(reductionIteratorUpdateStmt, syncThreadsStmt2);

            //Add the reduction loop after first __syncthreads() call
            kernelBody.addStatementAfter(syncThreadsStmt, reductionLoop);

            /**
             * Create special statement for thread 0
             */

            IfStatement reductionSpecialCondition = new IfStatement(
                    new BinaryExpression(new NameID(CUDA_THREAD_ID_X), BinaryOperator.COMPARE_EQ, new IntegerLiteral(0)),
                    new CompoundStatement()
            );

            CompoundStatement reductionSpecialBody= (CompoundStatement)reductionSpecialCondition.getThenStatement();

            //Return partial reduction result to global memory
            for(String reductionOp:reductionVariables.keySet())
            {
                for(String reductionVar: reductionVariables.get(reductionOp))
                {
                    String redVarName = "__shared_"+reductionVar;
                    String gpuRedVarName = CUDA_PREFIX + reductionVar;

                    if(reductionOp.compareTo("+") == 0)
                    {
                        reductionSpecialBody.addStatement(
                                new ExpressionStatement(new AssignmentExpression(
                                        new ArrayAccess(new NameID(gpuRedVarName), new NameID("__blockId")),
                                        AssignmentOperator.NORMAL,
                                        new ArrayAccess(new NameID(redVarName), new IntegerLiteral(0))
                                        )
                                )
                        );
                    }
                }
            }
            kernelBody.addStatementAfter(reductionLoop, reductionSpecialCondition);

            /**
             * Declare loop variable
             */
            List<Expression> indexVarList = LoopTools.collectIndexVariables(kernelLoop);
            for(Expression var : indexVarList)
            {
                Identifier indexVar = (Identifier)var;

                VariableDeclarator indexDeclarator = new VariableDeclarator(indexVar);
                kernelBody.addDeclaration(new VariableDeclaration(indexVar.getSymbol().getTypeSpecifiers(),
                        indexDeclarator));
            }

            ForLoop targetLoop;
            List<ForLoop> loops = LoopTools.collectForLoops(kernelLoop);

            /**
             * If loop is perfectly nested, convert innermost loop to use thread id instead of loop index
             * else convert outermost loop to use thread id instead of loop index
             */
            if(LoopTools.isPerfectNest(kernelLoop))
            {
                targetLoop = loops.get(loops.size()-1);
            }
            else
            {
                targetLoop = loops.get(0);
            }

            Expression lowerBoundExpression = LoopTools.getLowerBoundExpression(targetLoop);
            Expression upperBoundExpression = LoopTools.getUpperBoundExpression(targetLoop);

            Symbol targetLoopIndexSymbol = LoopTools.getLoopIndexSymbol(targetLoop);
            VariableDeclaration targetLoopVarDeclaration = (VariableDeclaration)SymbolTools.findSymbol(kernelBody, targetLoopIndexSymbol.getSymbolName());
            VariableDeclarator targetLoopVarDeclarator = (VariableDeclarator)targetLoopVarDeclaration.getDeclarator(0);

            Initializer initializer = new Initializer(Symbolic.add(threadIdDeclarator.getID(),lowerBoundExpression));
            targetLoopVarDeclarator.setInitializer(initializer);

            /**
             * Add condition for upperbound
             */
            Expression condition = targetLoop.getCondition().clone();
            IfStatement upperCondition = new IfStatement(Symbolic.negate(condition), new ReturnStatement());
            kernelBody.addStatementBefore(kernelLoop, upperCondition);

            /**
             * Remove inner loop
             */
            CompoundStatement innermostLoopParent = (CompoundStatement) targetLoop.getParent();
            innermostLoopParent.addStatementAfter(targetLoop, targetLoop.getBody().clone());
            innermostLoopParent.removeChild(targetLoop);

            /**
             * Compute the size of CUDA grid
             * TODO: Support multidimensional partitioning
             * TODO: Add heuristic algorithm to determine block and grid size
             *       based on device parameter e.g. number of SM, shared memory size
             */
            Expression innerLoopIterationCount = Symbolic.add(Symbolic.subtract(upperBoundExpression, lowerBoundExpression), new IntegerLiteral(1));
            cudaGridSizeX = Symbolic.add(Symbolic.divide(innerLoopIterationCount, new IntegerLiteral(cudaThreadBlockSizeX)), new IntegerLiteral(1));
        }
        else
        {
            throw new RuntimeException("Current Implementation support only For Loop");
        }

        /**
         *  Create kernel function declaration
         */
        Declarator accFunctionDeclarator = new ProcedureDeclarator(new NameID(kernelName), new LinkedList());

        for(Declaration param : parameterList)
        {
            accFunctionDeclarator.addParameter(param);
        }

        Procedure accFunction = new Procedure(returnSpec, accFunctionDeclarator, kernelBody);

        TranslationUnit translationUnit = (TranslationUnit)proc.getParent();
        translationUnit.addDeclarationBefore(proc, accFunction);

        /**
         * Create gridBlock size
         * TODO: Add support for multidimensional partitioning
         */
        CudaDim3Specifier dim3GridSpec = new CudaDim3Specifier(cudaGridSizeX, cudaGridSizeY, cudaGridSizeZ);
        VariableDeclarator dimGridDeclarator = new VariableDeclarator(new NameID("dimGrid_"+kernelName), dim3GridSpec);
        Identifier dimGrid = new Identifier(dimGridDeclarator);
        Declaration dimGridDeclaration = new VariableDeclaration(CudaSpecifier.CUDA_DIM3, dimGridDeclarator);
        parentStmt.addStatementBefore(curStmt, new DeclarationStatement(dimGridDeclaration));

        /**
         * Create threadBlock size
         * TODO: Add support for multidimensional partitioning
         */
        CudaDim3Specifier dim3BlockSpec = new CudaDim3Specifier(new IntegerLiteral(cudaThreadBlockSizeX), new IntegerLiteral(1),new IntegerLiteral(1));
        VariableDeclarator dimBlockDeclarator = new VariableDeclarator(new NameID("dimBlock_"+kernelName), dim3BlockSpec);
        Identifier dimBlock = new Identifier(dimBlockDeclarator);
        Declaration dimBlockDeclaration = new VariableDeclaration(CudaSpecifier.CUDA_DIM3, dimBlockDeclarator);
        parentStmt.addStatementBefore(curStmt, new DeclarationStatement(dimBlockDeclaration));


        /**
         * Create kernel function call
         */
        CudaKernelCall kernelCall = new CudaKernelCall(new NameID(kernelName), new ArrayList());

        for(Expression arg : argumentList)
        {
            kernelCall.addArgument(arg);
        }

        for(String reductionOp:reductionVariables.keySet())
        {
            for(String reductionVar: reductionVariables.get(reductionOp))
            {
                String gpuRedVarName = CUDA_PREFIX + reductionVar;
                kernelCall.addArgument(new NameID(gpuRedVarName));
            }
        }

        kernelCall.setGridSize(dimGrid);
        kernelCall.setBlockSize(dimBlock);

        OMPDTools.convertToOmpdProcId(kernelCall);

        ExpressionStatement kernelCallStmt = new ExpressionStatement(kernelCall);
        parentStmt.addStatementAfter(curStmt, kernelCallStmt);

        /**
         * Generate CPU code to compute
         */
        VariableDeclarator reductionSize = new VariableDeclarator(new NameID("red__count_" + kernelName));
        ValueInitializer reductionSizeInitializer = new ValueInitializer(cudaGridSizeX.clone());
        reductionSize.setInitializer(reductionSizeInitializer);

        DeclarationStatement reductionSizeDeclStmt = new DeclarationStatement(new VariableDeclaration(Specifier.INT, reductionSize));
        parentStmt.addStatementBefore(kernelCallStmt, reductionSizeDeclStmt);

        VariableDeclarator reductionIter = new VariableDeclarator(new NameID("red__i_" + kernelName));
        ValueInitializer reductionIterInitializer = new ValueInitializer(new IntegerLiteral(0));
        reductionIter.setInitializer(reductionIterInitializer);

        DeclarationStatement reductionIterDeclStmt = new DeclarationStatement(new VariableDeclaration(Specifier.INT, reductionIter));
        parentStmt.addStatementBefore(kernelCallStmt, reductionIterDeclStmt);

        ForLoop reductionLoop = new ForLoop(
                new ExpressionStatement(new AssignmentExpression(new NameID("red__i_" + kernelName), AssignmentOperator.NORMAL, new IntegerLiteral(0))),
                new BinaryExpression(new NameID("red__i_" + kernelName), BinaryOperator.COMPARE_LT, new NameID("red__count_" + kernelName)),
                new UnaryExpression(UnaryOperator.POST_INCREMENT, new NameID("red__i_" + kernelName)),
                new CompoundStatement()
        );
        parentStmt.addStatementAfter(kernelCallStmt, reductionLoop);

        CompoundStatement reductionStmt = (CompoundStatement)reductionLoop.getBody();
        for(String reductionOp:reductionVariables.keySet())
        {
            for(String reductionVar: reductionVariables.get(reductionOp))
            {
                String redVarName = "red__" + reductionVar;

                if(reductionOp.compareTo("+") == 0)
                {
                    AssignmentExpression reductionExpr = new AssignmentExpression(
                        new NameID(reductionVar),
                        AssignmentOperator.ADD,
                        new ArrayAccess(new NameID(redVarName), new NameID("red__i_" + kernelName))
                    );
                    reductionStmt.addStatement(new ExpressionStatement(reductionExpr));
                }
            }
        }

        /**
         * Generate memory allocation, transfer and deallocation for reduction variable
         */
        for(String reductionOp:reductionVariables.keySet())
        {
            for(String reductionVar: reductionVariables.get(reductionOp))
            {
                //Allocation
                String cpuRedVarName = "red__" + reductionVar;
                String gpuRedVarName = CUDA_PREFIX + reductionVar;

                Set<Symbol> tables = proc.getSymbols();
                Symbol redVarSymbol = SymbolTools.getSymbolOfName(reductionVar, ((Statement) annot.getAnnotatable()).getParent());
                List<Specifier> globalRedVarSpecList = new ArrayList<Specifier>();
                VariableDeclaration redVarDeclaration = (VariableDeclaration)redVarSymbol.getDeclaration();
                globalRedVarSpecList.addAll(redVarDeclaration.getSpecifiers());
                globalRedVarSpecList.add(PointerSpecifier.UNQUALIFIED);

                //CPU
                VariableDeclarator cpuRedVarDeclarator = new VariableDeclarator(new NameID(cpuRedVarName));

                FunctionCall mallocCall = new FunctionCall(new NameID("malloc"),
                        new BinaryExpression(new SizeofExpression(redVarDeclaration.getSpecifiers()),
                                BinaryOperator.MULTIPLY,
                                new NameID("red__count_" + kernelName))
                );

                ValueInitializer cpuRedVarInitializer = new ValueInitializer(new Typecast(globalRedVarSpecList, mallocCall));
                cpuRedVarDeclarator.setInitializer(cpuRedVarInitializer);

                DeclarationStatement cpuRedVarDeclStmt = new DeclarationStatement(new VariableDeclaration(globalRedVarSpecList, cpuRedVarDeclarator));
                parentStmt.addStatementBefore(kernelCallStmt, cpuRedVarDeclStmt);

                //GPU
                VariableDeclarator gpuRedVarDeclarator = new VariableDeclarator(new NameID(gpuRedVarName));
                DeclarationStatement gpuRedVarDeclStmt = new DeclarationStatement(new VariableDeclaration(globalRedVarSpecList, gpuRedVarDeclarator));
                parentStmt.addStatementBefore(kernelCallStmt, gpuRedVarDeclStmt);

                AccMemoryAllocation redMemAlloc = new CudaMemoryAllocation(null, gpuRedVarDeclarator,
                        1,Arrays.asList((Expression)new NameID("red__count_"  + kernelName)),
                        null,
                        CudaMemoryAllocation.AllocationType.CUDA_MALLOC);

                redMemAlloc.generateMemoryAllocationCode(parentStmt, gpuRedVarDeclStmt);

                //Transfer result from GPU to CPU
                Expression cpuAddressExpression = new UnaryExpression(UnaryOperator.ADDRESS_OF, new ArrayAccess(new NameID(cpuRedVarName), new IntegerLiteral(0)));
                Expression gpuAddressExpression = new UnaryExpression(UnaryOperator.ADDRESS_OF, new ArrayAccess(new NameID(gpuRedVarName), new IntegerLiteral(0)));

                Expression sizeExpression = new BinaryExpression(new SizeofExpression(redVarDeclaration.getSpecifiers()),
                        BinaryOperator.MULTIPLY,
                        new NameID("red__count_"  + kernelName));

                FunctionCall cudaMemcpyCall = new FunctionCall(new NameID(CudaMemoryTransfer.CUDA_MEMCPY),
                    cpuAddressExpression,gpuAddressExpression,sizeExpression,new NameID(CudaMemoryTransfer.CUDA_MEMCPY_D2H));

                Statement cudaMemcpyCallStmt = new ExpressionStatement(cudaMemcpyCall);
                parentStmt.addStatementAfter(kernelCallStmt, cudaMemcpyCallStmt);

                //Deallocation
                FunctionCall cudaMemfreeCall = new FunctionCall(new NameID(CudaMemoryFree.CUDA_MEM_FREE), new NameID(gpuRedVarName));
                parentStmt.addStatementAfter(cudaMemcpyCallStmt, new ExpressionStatement(cudaMemfreeCall));
            }
        }

        /**
         * Remove parallel loop
         */
        parentStmt.removeStatement(curStmt);
    }
}
