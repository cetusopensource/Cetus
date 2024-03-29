package omp2gpu.analysis;

import java.io.*;
import java.util.*;
import java.lang.String;
import cetus.hir.*;

public class CudaParser
{
	private static String [] token_array;
	private static int token_index;
	private	static HashMap cuda_map;
	private int debug_level;

	public CudaParser() {
	}

	private static String get_token()
	{
		return token_array[token_index++];
	}

	private static void eat()
	{
		token_index++;
	}

	private static boolean match(String istr)
	{
		boolean answer = check(istr);
		if (answer == false) {
			System.out.println("CudaParser Syntax Error");
			System.out.println(display_tokens());
		}
		token_index++;
		return answer;
	}
	private static boolean check(String istr)
	{
		if ( end_of_token() ) 
			return false;
		return ( token_array[token_index].compareTo(istr) == 0 ) ? true : false;
	}	

	private static String display_tokens()
	{
		StringBuilder str = new StringBuilder(160);

		for (int i=0; i<token_array.length; i++)
		{
			str.append("token_array[" + i + "] = " + token_array[i] + "\n");
		}
		return str.toString();
	}

	private static boolean end_of_token()
	{
		return (token_index >= token_array.length) ? true : false;
	}

	public static boolean parse_cuda_pragma(HashMap input_map, String [] str_array)
	{
		cuda_map = input_map;
		token_array = str_array;
		token_index = 1; 

		PrintTools.println(display_tokens(), 9);

		String construct = "cuda_" + get_token();
		switch (cuda_pragma.valueOf(construct)) {
			case cuda_ainfo 		: parse_cuda_ainfo(); return true;
			case cuda_gpurun 		: parse_cuda_gpurun(); return true;
			case cuda_cpurun		: parse_cuda_cpurun(); return true;
			case cuda_nogpurun 		: parse_cuda_nogpurun(); return true;
			case cuda_enclosingloops 		: parse_cuda_enclosingloops(); return true;
			default : CudaParserError("Not Supported Construct");
		}
		return true;		
	}
	private static void parse_cuda_ainfo()
	{
		PrintTools.println("CudaParser is parsing [ainfo] directive", 2);
		addToMap("ainfo", "true");
		
		while (end_of_token() == false) 
		{
			String clause = "token_" + get_token();
			PrintTools.println("clause=" + clause, 2);
			switch (cuda_clause.valueOf(clause)) {
			case token_procname		:	parse_cuda_procname(); break;
			case token_kernelid	:	parse_cuda_kernelid(); break;
			default : CudaParserError("NoSuchCudaConstruct : " + clause);
			}
		}
	}

	private static void parse_cuda_gpurun()
	{
		PrintTools.println("CudaParser is parsing [gpurun] directive", 2);
		addToMap("gpurun", "true");

		while (end_of_token() == false) 
		{
			String clause = "token_" + get_token();
			PrintTools.println("clause=" + clause, 2);
			switch (cuda_clause.valueOf(clause)) {
			case token_c2gmemtr		:	parse_cuda_c2gmemtr(); break;
			case token_noc2gmemtr	:	parse_cuda_noc2gmemtr(); break;
			case token_g2cmemtr		:	parse_cuda_g2cmemtr(); break;
			case token_nog2cmemtr	:	parse_cuda_nog2cmemtr(); break;
			case token_registerRO		:	parse_cuda_registerRO(); break;
			case token_registerRW		:	parse_cuda_registerRW(); break;
			case token_noregister		:	parse_cuda_noregister(); break;
			case token_sharedRO 		:	parse_cuda_sharedRO(); break;
			case token_sharedRW 		:	parse_cuda_sharedRW(); break;
			case token_noshared 		:	parse_cuda_noshared(); break;
			case token_texture 		:	parse_cuda_texture(); break;
			case token_notexture 		:	parse_cuda_notexture(); break;
			case token_constant		:	parse_cuda_constant(); break;
			case token_noconstant		:	parse_cuda_noconstant(); break;
			case token_maxnumofblocks		:	parse_cuda_maxnumofblocks(); break;
			case token_noreductionunroll	:	parse_cuda_noreductionunroll(); break;
			case token_nocudamalloc	:	parse_cuda_nocudamalloc(); break;
			case token_nocudafree	:	parse_cuda_nocudafree(); break;
			case token_cudafree	:	parse_cuda_cudafree(); break;
			case token_noploopswap	:	addToMap("noploopswap", "true"); break;
			case token_noloopcollapse	:	addToMap("noloopcollapse", "true"); break;
			case token_threadblocksize		:	parse_cuda_threadblocksize(); break;
			case token_multisrccg	:	parse_cuda_multisrccg(); break;
			case token_multisrcgc	:	parse_cuda_multisrcgc(); break;
			case token_conditionalsrc	:	parse_cuda_conditionalsrc(); break;
			default : CudaParserError("NoSuchCudaConstruct : " + clause);
			}
		}
	}
	
	private static void parse_cuda_nogpurun()
	{
		PrintTools.println("CudaParser is parsing [nogpurun] directive", 2);
		addToMap("nogpurun", "true");
		
		while (end_of_token() == false) 
		{
			String clause = "token_" + get_token();
			PrintTools.println("[WARNING] any clause (" + clause +") attached to " +
					"cuda nogpurun will be ignored", 0);
		}
	}
	
	private static void parse_cuda_enclosingloops()
	{
		PrintTools.println("CudaParser is parsing [enclosingloops] directive", 2);
		match("(");
		Set set = new LinkedHashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("enclosingloops", set);
		
		while (end_of_token() == false) 
		{
			String clause = "token_" + get_token();
			PrintTools.println("[WARNING] any clause (" + clause +") attached to " +
					"cuda enclosingloops will be ignored", 0);
		}
	}
	

	public static HashMap<String,HashMap<String, Object>> parse_cuda_userdirective(String[] str_array)
	{
		cuda_map = new HashMap<String, Object>();
		HashMap userDirectives = new HashMap<String, HashMap<String, Object>>();
		token_array = str_array;
		token_index = 0; 
		PrintTools.println(display_tokens(), 9);

		PrintTools.println("CudaParser is parsing user-directves", 2);
		String kernelid = null;
		String procname = null;
		String kernelname = null;
		String clause = "token_" + get_token();
		if( clause.equals("token_kernelid") ) {
			match("(");
			kernelid = get_token();
			match(")");
		} else {
			PrintTools.println("[ERROR in parse_cuda_userdirective()] kernelid is missing; " +
					"current user directive line will be ignored.", 0);
			PrintTools.println("Current token is " + clause, 0);
			return null;
		}
		clause = "token_" + get_token();
		if( clause.equals("token_procname") ) {
			match("(");
			procname = get_token();
			match(")");
		} else {
			PrintTools.println("[ERROR in parse_cuda_userdirective()] procname is missing; " +
					"current user directive line will be ignored.", 0);
			return null;
		}
		kernelname = procname.concat(kernelid);

		while (end_of_token() == false) 
		{
			clause = "token_" + get_token();
			PrintTools.println("clause=" + clause, 2);
			switch (cuda_clause.valueOf(clause)) {
			case token_nogpurun		:	parse_cuda_nogpurun(); break;
			case token_c2gmemtr		:	parse_cuda_c2gmemtr(); break;
			case token_noc2gmemtr	:	parse_cuda_noc2gmemtr(); break;
			case token_g2cmemtr		:	parse_cuda_g2cmemtr(); break;
			case token_nog2cmemtr	:	parse_cuda_nog2cmemtr(); break;
			case token_registerRO		:	parse_cuda_registerRO(); break;
			case token_registerRW		:	parse_cuda_registerRW(); break;
			case token_noregister		:	parse_cuda_noregister(); break;
			case token_sharedRO 		:	parse_cuda_sharedRO(); break;
			case token_sharedRW 		:	parse_cuda_sharedRW(); break;
			case token_noshared 		:	parse_cuda_noshared(); break;
			case token_texture 		:	parse_cuda_texture(); break;
			case token_notexture 		:	parse_cuda_notexture(); break;
			case token_constant		:	parse_cuda_constant(); break;
			case token_noconstant		:	parse_cuda_noconstant(); break;
			case token_maxnumofblocks		:	parse_cuda_maxnumofblocks(); break;
			case token_noreductionunroll	:	parse_cuda_noreductionunroll(); break;
			case token_nocudamalloc	:	parse_cuda_nocudamalloc(); break;
			case token_nocudafree	:	parse_cuda_nocudafree(); break;
			case token_cudafree	:	parse_cuda_cudafree(); break;
			case token_noploopswap	:	addToMap("noploopswap", "true"); break;
			case token_noloopcollapse	:	addToMap("noloopcollapse", "true"); break;
			case token_threadblocksize		:	parse_cuda_threadblocksize(); break;
			default : CudaParserError("NoSuchCudaConstruct : " + clause);
			}
		}
		userDirectives.put(kernelname, cuda_map);
		return userDirectives;
	}
	
	
	public static HashMap<String,Object> parse_cuda_tuningconfig(String[] str_array)
	{
		cuda_map = new HashMap<String, Object>();
		token_array = str_array;
		token_index = 0; 
		PrintTools.println(display_tokens(), 9);

		PrintTools.println("CudaParser is parsing default tuning configuration", 2);
		String clause = null;

		while (end_of_token() == false) 
		{
			clause = "conf_" + get_token();
			PrintTools.println("clause=" + clause, 2);
			switch (cuda_tuningconf.valueOf(clause)) {
			case conf_defaultGOptionSet		:	parse_conf_defaultGOptionSet(); break;
			case conf_excludedGOptionSet		:	parse_conf_excludedGOptionSet(); break;
			case conf_cudaMemTrOptLevel	:	parse_conf_cudaMemTrOptLevel(); break;
			case conf_cudaMallocOptLevel		:	parse_conf_cudaMallocOptLevel(); break;
			case conf_cudaThreadBlockSet		:	parse_conf_cudaThreadBlockSet(); break;
			case conf_maxnumofblocksSet		:	parse_conf_maxnumofblocksSet(); break;
			case conf_UEPRemovalOptLevel		:	parse_conf_UEPRemovalOptLevel(); break;
			default : CudaParserError("NoSuchCudaConstruct : " + clause);
			}
		}
		return cuda_map;
	}

	private static void parse_cuda_cpurun()
	{
		PrintTools.println("CudaParser is parsing [cpurun] clause", 2);
		addToMap("cpurun", "true");
		
		while (end_of_token() == false) 
		{
			String clause = "token_" + get_token();
			PrintTools.println("clause=" + clause, 2);
			switch (cuda_clause.valueOf(clause)) {
			case token_c2gmemtr		:	parse_cuda_c2gmemtr(); break;
			case token_noc2gmemtr	:	parse_cuda_noc2gmemtr(); break;
			case token_g2cmemtr		:	parse_cuda_g2cmemtr(); break;
			case token_nog2cmemtr	:	parse_cuda_nog2cmemtr(); break;
			default : CudaParserError("NoSuchCudaConstruct : " + clause);
			}
		}
	}



	private static void parse_cuda_c2gmemtr()
	{
		PrintTools.println("CudaParser is parsing [c2gmemtr] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("c2gmemtr", set);
	}

	private static void parse_cuda_noc2gmemtr()
	{
		PrintTools.println("CudaParser is parsing [noc2gmemtr] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("noc2gmemtr", set);
	}
	
	private static void parse_cuda_g2cmemtr()
	{
		PrintTools.println("CudaParser is parsing [g2cmemtr] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("g2cmemtr", set);
	}
	
	private static void parse_cuda_nog2cmemtr()
	{
		PrintTools.println("CudaParser is parsing [nog2cmemtr] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("nog2cmemtr", set);
	}
	
	private static void parse_cuda_registerRO()
	{
		PrintTools.println("CudaParser is parsing [registerRO] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("registerRO", set);
	}
	
	private static void parse_cuda_registerRW()
	{
		PrintTools.println("CudaParser is parsing [registerRW] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("registerRW", set);
	}
	
	private static void parse_cuda_noregister()
	{
		PrintTools.println("CudaParser is parsing [noregister] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("noregister", set);
	}
	
	private static void parse_cuda_sharedRO()
	{
		PrintTools.println("CudaParser is parsing [sharedRO] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("sharedRO", set);
	}
	
	private static void parse_cuda_sharedRW()
	{
		PrintTools.println("CudaParser is parsing [sharedRW] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("sharedRW", set);
	}
	
	private static void parse_cuda_noshared()
	{
		PrintTools.println("CudaParser is parsing [noshared] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("noshared", set);
	}
	
	private static void parse_cuda_texture()
	{
		PrintTools.println("CudaParser is parsing [texture] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("texture", set);
	}
	
	private static void parse_cuda_notexture()
	{
		PrintTools.println("CudaParser is parsing [notexture] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("notexture", set);
	}
	
	private static void parse_cuda_constant()
	{
		PrintTools.println("CudaParser is parsing [constant] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("constant", set);
	}
	
	private static void parse_cuda_noconstant()
	{
		PrintTools.println("CudaParser is parsing [noconstant] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("noconstant", set);
	}
	
	private static void parse_cuda_maxnumofblocks()
	{
		PrintTools.println("CudaParser is parsing [maxnumofblocks] clause", 2);
		match("(");
		String maxNumOfBlocks = get_token();
		match(")");
		addToMap("maxnumofblocks", maxNumOfBlocks);
	}
	
	private static void parse_cuda_threadblocksize()
	{
		PrintTools.println("CudaParser is parsing [threadblocksize] clause", 2);
		match("(");
		String threadblocksize = get_token();
		match(")");
		addToMap("threadblocksize", threadblocksize);
	}
	
	private static void parse_cuda_noreductionunroll()
	{
		PrintTools.println("CudaParser is parsing [noreductionunroll] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("noreductionunroll", set);
	}
	
	private static void parse_cuda_nocudamalloc()
	{
		PrintTools.println("CudaParser is parsing [nocudamalloc] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("nocudamalloc", set);
	}
	
	private static void parse_cuda_nocudafree()
	{
		PrintTools.println("CudaParser is parsing [nocudafree] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("nocudafree", set);
	}
	
	private static void parse_cuda_cudafree()
	{
		PrintTools.println("CudaParser is parsing [cudafree] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("cudafree", set);
	}
	
	private static void parse_cuda_multisrccg()
	{
		PrintTools.println("CudaParser is parsing [multisrccg] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("multisrccg", set);
	}
	
	private static void parse_cuda_multisrcgc()
	{
		PrintTools.println("CudaParser is parsing [multisrcgc] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("multisrcgc", set);
	}
	
	private static void parse_cuda_conditionalsrc()
	{
		PrintTools.println("CudaParser is parsing [conditionalsrc] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("conditionalsrc", set);
	}
	
	private static void parse_cuda_procname()
	{
		PrintTools.println("CudaParser is parsing [procname] clause", 2);
		match("(");
		String procname = get_token();
		match(")");
		addToMap("procname", procname);
	}
	
	private static void parse_cuda_kernelid()
	{
		PrintTools.println("CudaParser is parsing [kernelid] clause", 2);
		match("(");
		String kernelid = get_token();
		match(")");
		addToMap("kernelid", kernelid);
	}
	
	private static void parse_conf_defaultGOptionSet()
	{
		PrintTools.println("CudaParser is parsing [defaultGOptionSet] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("defaultGOptionSet", set);
	}
	
	private static void parse_conf_excludedGOptionSet()
	{
		PrintTools.println("CudaParser is parsing [excludedGOptionSet] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("excludedGOptionSet", set);
	}
	
	private static void parse_conf_cudaThreadBlockSet()
	{
		PrintTools.println("CudaParser is parsing [cudaThreadBlockSet] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("cudaThreadBlockSet", set);
	}
	
	private static void parse_conf_maxnumofblocksSet()
	{
		PrintTools.println("CudaParser is parsing [maxnumofblocksSet] clause", 2);
		match("(");
		Set set = new HashSet<String>();
		parse_commaSeparatedList(set);
		match(")");
		addToMap("maxnumofblocksSet", set);
	}
	
	private static void parse_conf_cudaMemTrOptLevel()
	{
		PrintTools.println("CudaParser is parsing [cudaMemTrOptLevel] clause", 2);
		match("=");
		addToMap("cudaMemTrOptLevel", get_token());
	}
	
	private static void parse_conf_cudaMallocOptLevel()
	{
		PrintTools.println("CudaParser is parsing [cudaMemTrOptLevel] clause", 2);
		match("=");
		addToMap("cudaMallocOptLevel", get_token());
	}
	
	private static void parse_conf_UEPRemovalOptLevel()
	{
		PrintTools.println("CudaParser is parsing [UEPRemovalOptLevel] clause", 2);
		match("=");
		addToMap("UEPRemovalOptLevel", get_token());
	}
	
	private static void parse_commaSeparatedList(Set set)
	{
		for (;;) {
			set.add(get_token());
			if ( check(")") )
			{
				break;
			}
			else if ( match(",") == false )
			{
				CudaParserError("comma expected in comma separated list");
			}
		}
	}

	private static void notSupportedWarning(String text)
	{
		System.out.println("Not Supported Cuda Annotation: " + text); 
	}

	private static void CudaParserError(String text)
	{
		System.out.println("Cuda Parser Syntax Error: " + text);
		System.out.println(display_tokens());
	}

	private static void addToMap(String key, String new_str)
	{
		if (cuda_map.keySet().contains(key))
			Tools.exit("[ERROR] Cuda Parser detected duplicate pragma: " + key);
		else
			cuda_map.put(key, new_str);
	}

	private static void addToMap(String key, Set new_set)
	{
		if (cuda_map.keySet().contains(key))
		{
			Set set = (Set)cuda_map.get(key);
			set.addAll(new_set);
		}
		else
		{
			cuda_map.put(key, new_set);
		}
	}

	private static void addToMap(String key, Map new_map)
	{
		if (cuda_map.keySet().contains(key))
		{
			Map orig_map = (Map)cuda_map.get(key);
			for ( String new_str : (Set<String>)new_map.keySet() )
			{
				Set new_set = (Set)new_map.get(new_str);
				if (orig_map.keySet().contains(new_str))
				{
					Set orig_set = (Set)orig_map.get(new_str);
					orig_set.addAll(new_set);
				}
				else
				{
					orig_map.put(new_str, new_set);
				}
			}
		}
		else
		{
			cuda_map.put(key, new_map);
		}
	}

	public static enum cuda_pragma
	{
		cuda_ainfo, 
		cuda_gpurun, 
		cuda_cpurun,
		cuda_nogpurun,
		cuda_enclosingloops
	}

	public static enum cuda_clause
	{
		token_c2gmemtr,
		token_noc2gmemtr,
		token_g2cmemtr,
		token_nog2cmemtr,
		token_registerRO,
		token_registerRW,
		token_noregister,
		token_sharedRO,
		token_sharedRW,
		token_noshared,
		token_texture,
		token_notexture,
		token_constant,
		token_noconstant,
		token_maxnumofblocks,
		token_noreductionunroll,
		token_nocudamalloc,
		token_nocudafree,
		token_cudafree,
		token_procname,
		token_kernelid,
		token_noploopswap,
		token_noloopcollapse,
		token_threadblocksize,
		token_nogpurun,
		token_multisrccg,
		token_multisrcgc,
		token_conditionalsrc
	}
	
	public static enum cuda_tuningconf
	{
		conf_defaultGOptionSet,
		conf_excludedGOptionSet,
		conf_cudaMemTrOptLevel,
		conf_cudaMallocOptLevel,
		conf_cudaThreadBlockSet,
		conf_maxnumofblocksSet,
		conf_UEPRemovalOptLevel
	}

}
