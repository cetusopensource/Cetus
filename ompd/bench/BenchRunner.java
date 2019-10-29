package bench;

import cetus.hir.Tools;

import java.util.*;
import java.util.regex.*;
import java.io.*;
import java.text.SimpleDateFormat;
import java.util.concurrent.*;

import org.w3c.dom.*;

import javax.xml.XMLConstants;
import javax.xml.parsers.*;

import org.xml.sax.*;

import javax.xml.transform.*;
import javax.xml.transform.stream.*;
import javax.xml.transform.dom.*;
import javax.xml.validation.*;

/**
 * <code>BenchRunner</code> performs a series of tasks defined by the input
 * configuration file. It invokes a typical sequence of tasks that performs
 * source-code translation with cetus, compilation of the cetus' output with a
 * back-end compiler, and execution of the resulting binary code. An input XML
 * file is passed to the driver, {@link #main(String[])}, and parsed to drive the
 * benchmarking process. Simple result such as return status and runtime is
 * reported in the output XML file.
 * <p>[Input XML File]<p>
 * <code>BenchRunner</code> internally validates an input file against the XML
 * schema, <a href="http://cetus.ecn.purdue.edu/doc/ref">
 * http://cetus.ecn.purdue.edu/doc/ref/benchmark.xsd</a>. You can
 * find a full structure of a valid input file by following the provided link.
 * <p>[Invoking <code>BenchRunner</code>]<p>
 * To invoke a single <code>BenchRunner</code>, users need to prepare source
 * code (makefile is not required but preferred), input data for the program,
 * output reference data (if validation is required), and an input XML file to
 * the <code>BenchRunner</code> driver.
 * <p>[Output XML File]<p>
 * The result of a benchmarking process is generated in XML format by adding
 * the collected information to the original input XML file. This is a reasonable
 * way of generating output since the input file contains most accurate
 * information about a benchmarking process. Extracting information from this
 * output XML file should be an easy task since most major languages support
 * such a feature.
 */
public class BenchRunner
{
    /**
     * Constant strings
     */
    private static final String NEWLINE = System.getProperty("line.separator");
    private static final String FILESEP = File.separator;
    private static final String LISTSEP = "[;" + NEWLINE + "]+";
    private static final PrintStream SYSOUT = System.out;
    private static final PrintStream SYSERR = System.err;

    /**
     * Parsed benchmark configuration
     */
    private Map<String, String> info;

    /**
     * List of ordered tasks to be executed
     */
    private List<Task> tasks;

    /**
     * User's environment variables including ones in the input configuration
     */
    private Map<String, String> envs;

    /**
     * The root document that contains configuration
     */
    private Document bench_root;

    /**
     * The log/out stream
     */
    private PrintStream log, out;

    /**
     * The input file name
     */
    private String config_file;

    /**
     * Accepts configuration files.
     */
    public static void main(String[] args)
    {
        if (args.length != 1)
        {
            SYSERR.println(getTID() + "This driver takes only one xml file as input.");
            System.exit(1);
        }
        BenchRunner driver = null;
        try
        {
            driver = new BenchRunner(args[0]);
        }
        catch (Exception ex)
        {
            SYSERR.println(getTID() + "[ERROR] " + ex.getMessage());
            return;
        }
        driver.runTasks();
    }

    private static String getTID()
    {
        return "[" + Thread.currentThread().getId() + "]";
    }

    /**
     * Does nothing
     */
    public BenchRunner()
    {
    }

    /**
     * Constructs a new driver with the specified configuration.
     *
     * @param config_file the input xml file that contains the configuration.
     */
    public BenchRunner(String config_file) throws Exception
    {
        info = new HashMap<String, String>();
        tasks = new LinkedList<Task>();
        envs = new HashMap<String, String>();
        this.config_file = config_file;
        parseConfiguration();
    }

    /**
     * Runs the specified tasks. During this process, it should print out the
     * location of the log/out files for drivers, wrttien in other languages, to
     * identify the files. {@code ExecutorService} was used to enable time-out
     * mechanism.
     */
    public void runTasks()
    {
        SYSOUT.println("Invoking benchmark [" + info.get("name") + "] ...");
        SYSOUT.println("  [OUT] " + envs.get("OUT"));
        SYSOUT.println("  [LOG] " + envs.get("LOG"));
        for (Task task : tasks)
        {
            try
            {
                task.elapsed = Tools.getTime();
                task.call();
            }
            catch (Exception ex)
            {
                log.println("[ERROR] " + ex.getMessage());
                ex.printStackTrace(log);
                task.status = false;
            }
            finally
            {
                task.elapsed = Tools.getTime(task.elapsed);
                task.generateResult();
                if (!task.status)
                    break;
            }
        }
        log.close();
        SYSOUT.println("Writing result ...");
        writeDocument(out);
        out.close();
    }

    /**
     * Returns a normalized text contents tagged by the given tag name.
     *
     * @param parent the parent node where search starts from.
     * @param tag    the tag name to be searched for.
     * @return the child node found or null (if not found).
     */
    private static Node getChildWith(Node parent, String tag)
    {
        NodeList children = parent.getChildNodes();
        for (int i = 0; i < children.getLength(); i++)
        {
            Node child = children.item(i);
            if (child.getNodeType() != Node.ELEMENT_NODE)
                continue;
            if (child.getNodeName().equals(tag) && child.getTextContent().trim().length() > 0)
                return child;
        }
        return null;
    }

    /**
     * Writes back the configuration file with the benchmark result appended.
     *
     * @param p the target print stream.
     */
    private void writeDocument(PrintStream p)
    {
        try
        {
            Transformer tf = TransformerFactory.newInstance().newTransformer();
            //tf.setOutputProperty(OutputKeys.INDENT, "yes");
            StreamResult result = new StreamResult(p);
            DOMSource source = new DOMSource(bench_root);
            tf.transform(source, result);
        }
        catch (TransformerConfigurationException ex)
        {
            SYSERR.println(getTID() + ex.getMessage());
        }
        catch (TransformerException ex)
        {
            SYSERR.println(getTID() + ex.getMessage());
        }
    }

    /**
     * Checks if the parsed configuration contains the specified tag name.
     *
     * @param tag the tag name to be checked for existence.
     * @return true if it is defined as a non-empty string.
     */
    private boolean hasDefinition(String tag)
    {
        return (info.get(tag) != null && info.get(tag).length() > 0);
    }

    /**
     * Detects and replaces usage of environment variables in the specified string
     * input. It uses the map of environment variables/values that were already
     * loaded from the user's environment and from the configuration.
     *
     * @param str the given string object.
     * @return the result of the replacement.
     */
    private String replaceEnvs(String str)
    {
        Map<String, String> system_envs = System.getenv();
        String ret = str;
        List<String> matched_vars = new LinkedList<String>();
        Matcher env_matcher = Pattern.compile("\\$[A-Z_]+").matcher(ret);
        while (env_matcher.find())
        {
            String env = env_matcher.group();
            String env_name = env.substring(1);
            String value = envs.get(env_name);
            if (value == null)
                value = system_envs.get(env_name);
            if (value == null)
                throw new InternalError(env_name + " is not defined");
            ret = ret.replace(env, value);
        }
        return ret;
    }

    @Override
    public String toString()
    {
        StringBuilder sb = new StringBuilder(80);
        for (String tag : info.keySet())
        {
            sb.append(tag);
            sb.append(" => ");
            sb.append(info.get(tag));
            sb.append(NEWLINE);
        }
        for (Task task : tasks)
        {
            sb.append(task);
            sb.append(NEWLINE);
        }
        return sb.toString();
    }

    /**
     * Parses envrionment variables and "info" elements. This method performs the
     * following tasks.
     * 1. Caches the environment variables defined within the configuration file.
     * 2. Prepares channels for printing logs and outputs.
     * 3. Collects information from the configuration while expanding environment
     * variables.
     *
     * @param info_node the root node with "info" tag.
     */
    private void parseInfoNode(Node info_node)
    {
        // 1. Prepare environment variables first
        // Loads configuration's environments
        Node envs_node = getChildWith(info_node, "envs");
        if (envs_node != null)
        { // "envs" element is optional
            String[] envs_list = envs_node.getTextContent().split(LISTSEP);
            for (int i = 0; i < envs_list.length; i++)
            {
                int sep = envs_list[i].indexOf("=");
                envs.put(envs_list[i].substring(0, sep).trim(), envs_list[i].substring(sep + 1).trim().replaceAll("\"", ""));
            }
        }

        // 2. Prepare log channels.
        String prefix = getChildWith(info_node, "name").getTextContent().trim();
        prefix += ".";
        Node tag_node = getChildWith(info_node, "tag");
        if (tag_node != null)
            prefix += tag_node.getTextContent().trim();
        else // Date-based automatic tag is created in this case.
            prefix += (new SimpleDateFormat("MMddHHmmss")).format(new Date());
        prefix = System.getProperty("user.dir") + FILESEP + prefix;
        envs.put("LOG", prefix + ".log");
        envs.put("OUT", prefix + ".xml");
        try
        {
            log = new PrintStream(new File(envs.get("LOG")));
            out = new PrintStream(new File(envs.get("OUT")));
        }
        catch (FileNotFoundException ex)
        {
            SYSERR.println(getTID() + ex.getMessage());
        }

        // 3. Collect other information.
        NodeList nodes = info_node.getChildNodes();
        for (int i = 0; i < nodes.getLength(); i++)
        {
            Node node = nodes.item(i);
            if (node.getNodeType() == Node.ELEMENT_NODE)
            {
                String tag = node.getNodeName();
                String value = node.getTextContent().trim();
                String replaced = replaceEnvs(value);
                info.put(tag, replaced);
                if (!value.equals(replaced))
                    node.setTextContent(replaced);
            }
        }

        // 4. Default information
        if (!hasDefinition("dir"))
            info.put("dir", System.getProperty("user.dir"));

        // Adds detected information
        detectMachineInfo(info_node);
    }

    /**
     * Adds the specified information to the parent node after wrapping it with
     * a "metric" node.
     *
     * @param name   the tag name of a metric element.
     * @param value  the value a metric element.
     * @param parent the node that enclose the metric information.
     */
    private void addMetric(String name, String value, Node parent)
    {
        Node metric = getChildWith(parent, "metric");
        if (metric == null)
        {
            metric = bench_root.createElement("metric");
            parent.appendChild(metric);
        }
        metric.appendChild(createSimpleNode(name, value));
    }

    /**
     * Creates a simple node with the specified information.
     *
     * @param name  the tag name of the simple node.
     * @param value the value of the simple node.
     */
    private Node createSimpleNode(String name, String value)
    {
        Node ret = bench_root.createElement(name);
        ret.setTextContent(value);
        return ret;
    }

    /**
     * Adds predefined set of information to the specified parent node.
     *
     * @param info_node the node that encloses new information.
     */
    private void detectMachineInfo(Node info_node)
    {
        info_node.appendChild(createSimpleNode("java", System.getProperty("java.version")));
        info_node.appendChild(createSimpleNode("arch", System.getProperty("os.arch")));
        info_node.appendChild(createSimpleNode("os", System.getProperty("os.name")));
        info_node.appendChild(createSimpleNode("date", (new Date()).toString()));
    }

    /**
     * Parses the input file
     */
    private void parseConfiguration() throws Exception
    {
        DocumentBuilderFactory doc_factory = DocumentBuilderFactory.newInstance();
        // Validation method#1: xsd location appears in the XML file.
        // Just calling setValidating() assumes DTD not XML schema.
/*
    doc_factory.setNamespaceAware(true);
    doc_factory.setValidating(true);
    doc_factory.setAttribute(
        "http://java.sun.com/xml/jaxp/properties/schemaLanguage",
        "http://www.w3.org/2001/XMLSchema");
    DocumentBuilder doc_builder = doc_factory.newDocumentBuilder();
    doc_builder.setErrorHandler(new ParseErrorHandler());
    bench_root = doc_builder.parse(config_file);
    bench_root.normalizeDocument();
*/
        // Validation method#2: schema is defined in this application.
        DocumentBuilder doc_builder = doc_factory.newDocumentBuilder();
        bench_root = doc_builder.parse(config_file);
        bench_root.normalizeDocument();
        String XSD_URI = "http://aeug.ecn.purdue.edu/ref/benchmark.xsd";
        SchemaFactory schema_factory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
        Schema schema = schema_factory.newSchema(new StreamSource(XSD_URI));
        schema.newValidator().validate(new DOMSource(bench_root));

        NodeList nodes = bench_root.getDocumentElement().getChildNodes();
        for (int i = 0; i < nodes.getLength(); i++)
        {
            Node node = nodes.item(i);
            if (node.getNodeType() != Node.ELEMENT_NODE)
                continue;
            String node_name = node.getNodeName();
            if (node_name.equals("info"))
                parseInfoNode(node);
            else if (node_name.equals("cetus"))
                tasks.add(new Translator(node));
            else
                tasks.add(new Task(node));
        }
    }

    /**
     * Implementation of file filter for handling wild card character and other
     * special characters to generate regular expressions out of a string.
     */
    private static class RegexFilter implements FileFilter
    {
        /**
         * Regular expression
         */
        private String regex;

        /**
         * Constructs a new filter with the given input string
         */
        public RegexFilter(String str)
        {
            regex = str.replaceAll("\\.", "\\\\.") // . => \.
                    .replaceAll("\\?", ".")            // ? => .
                    .replaceAll("\\*", ".*");          // * => .*
        }

        @Override
        public boolean accept(File f)
        {
            return f.getName().matches(regex);
        }
    }

    /**
     * This class provides a simple thread object that pipes information from a
     * reader to a print stream.
     */
    private static class Pipe extends Thread
    {
        /**
         * The source of the stream
         */
        private BufferedReader from;

        /**
         * The destination of the stream
         */
        private PrintStream to;

        /**
         * Constructs a new pipe with the specified source and destination.
         *
         * @param from the buffered reader to be used as source.
         * @param to   the print stream to be used as destination.
         */
        Pipe(BufferedReader from, PrintStream to)
        {
            this.from = from;
            this.to = to;
        }

        @Override
        public void run()
        {
            String line = null;
            try
            {
                while ((line = from.readLine()) != null)
                    to.println(line);
            }
            catch (IOException ex)
            {
                to.println("Unable to pipe the IO stream: " + ex);
            }
        }
    }

    /**
     * This class implements a simple error handler to be used during the parsing
     * process of XML file.
     *
     * @see DocumentBuilder
     */
    private static class ParseErrorHandler implements ErrorHandler
    {
        ParseErrorHandler()
        {
        }

        // Just ignores warnings.
        public void warning(SAXParseException ex) throws SAXException
        {
            SYSERR.println(getTID() + "[WARNING] " + ex.getMessage());
        }

        public void error(SAXParseException ex) throws SAXException
        {
            throw ex; // up to the call stack.
        }

        public void fatalError(SAXParseException ex) throws SAXException
        {
            throw ex; // up to the call stack.
        }
    }

    /**
     * Individual tasks of a single run
     */
    private class Task implements Callable<Integer>
    {
        /**
         * The root node for this task
         */
        Node task_root;

        /**
         * Simple representation of tag-value pairs.
         */
        Map<String, String> tags;

        /**
         * Parameters used for invoking a process
         */
        String command;

        /**
         * The directory where the current task should start from.
         */
        File dir;

        /**
         * Exit status of this task
         */
        boolean status;

        /**
         * Elapsed time of this task
         */
        double elapsed;

        /**
         * Does nothing
         */
        Task()
        {
        }

        /**
         * Constructs a new task with the specified configuration.
         *
         * @param node the input document describing the task configuration.
         */
        Task(Node node)
        {
            tags = new HashMap<String, String>();
            tags.put("name", node.getNodeName());
            NodeList children = node.getChildNodes();
            for (int i = 0; i < children.getLength(); i++)
            {
                Node child = children.item(i);
                if (child.getNodeType() == Node.ELEMENT_NODE)
                {
                    String tag = child.getNodeName();
                    String value = child.getTextContent().trim();
                    String replaced = replaceEnvs(value);
                    tags.put(tag, replaced);
                    if (!value.equals(replaced))
                        child.setTextContent(replaced);
                }
            }
            task_root = node;
            status = true;
        }

        /**
         * Invokes the specified command line as a sub task of this task object.
         * This is the lowest-level handler that blindly invokes a process.
         *
         * @param cmd the command to be invoked.
         * @param out the target of the output stream.
         * @param err the target of the error stream.
         */
        void invokeProcess(String cmd, PrintStream out, PrintStream err)
        {
            List<String> args = Arrays.asList(cmd.trim().split(" +"));
            ProcessBuilder pb = new ProcessBuilder(args);
            pb.directory(dir);
            pb.environment().putAll(envs);
            Thread out_pipe = null, err_pipe = null;
            try
            {
                Process proc = pb.start();
                BufferedReader out_reader = new BufferedReader(new InputStreamReader(proc.getInputStream()));
                BufferedReader err_reader = new BufferedReader(new InputStreamReader(proc.getErrorStream()));
                out_pipe = new Pipe(out_reader, out);
                out_pipe.start();
                err_pipe = new Pipe(err_reader, err);
                err_pipe.start();
                out_pipe.join();
                err_pipe.join();
                status = (proc.waitFor() == 0);
            }
            catch (IOException ex)
            {
                SYSERR.println(getTID() + "Unable to start a child process.");
            }
            catch (InterruptedException ex)
            {
                SYSERR.println(getTID() + "Unable to join the child process.");
            }
        }

        @Override
        public Integer call()
        {
            // preparing necessary files
            prepareFiles();
            try
            {
                // preprocessing command
                if (hasDefinition("pre"))
                    invokeProcess(tags.get("pre"), log, log);
                // the main command for this task
                invokeCommand(log, log);
                // postprocessing command
                if (hasDefinition("post"))
                    invokeProcess(tags.get("post"), log, log);
            }
            catch (Exception ex)
            {
                status = false;
            }
            return null; // not used
        }

        /**
         * Invokes the core command of this task object.
         *
         * @param out the print stream to which standard output is redirected.
         * @param err the print stream to which standard wrror is redirected.
         */
        void invokeCommand(PrintStream out, PrintStream err)
        {
            invokeProcess(command, out, err);
        }

        /**
         * Performs file operations defined within the "dir" and "require" node.
         */
        void prepareFiles()
        {
            if (tags.get("dir").startsWith(FILESEP)) // absolute path
                dir = new File(tags.get("dir"));
            else
                dir = new File(info.get("dir"), tags.get("dir"));
            if (!dir.exists() && !dir.mkdir())
                throw new InternalError("cannot create " + dir.getAbsolutePath());
            command = tags.get("command");
            // Copies the required files into the working directory
            if (!hasDefinition("require"))
                return;
            String[] files = tags.get("require").split(LISTSEP);
            for (String file : files)
            {
                int last_sep = file.lastIndexOf(FILESEP);
                if (last_sep == -1)
                    throw new InternalError("cannot copy required files");
                File location = null;
                String path = file.substring(0, last_sep);
                String fname = file.substring(last_sep + 1);
                if (file.startsWith(FILESEP)) // absolute path
                    location = new File(path);
                else
                    location = new File(info.get("dir"), path);
                // expands wild cards and performs copy operations
                for (File final_file : location.listFiles(new RegexFilter(fname)))
                    invokeProcess("cp -r " + final_file.getPath() + " .", null, null);
            }
        }

        /**
         * Generates simple result of this task.
         */
        void generateResult()
        {
            SYSOUT.print("  [" + tags.get("name") + "] ...... ");
            SYSOUT.print((status) ? "PASS" : "FAIL");
            SYSOUT.println(String.format(" %.2f seconds", elapsed));
            addMetric("pass", Boolean.toString(status), task_root);
            addMetric("walltime", String.format("%.2f", elapsed), task_root);
        }

        /**
         * Adds any valid string in the array of strings and returns true.
         * Returns false if all strings are invalid.
         *
         * @param ret  the returned string builder.
         * @param strs the array of strings to be tested for addition.
         */
        protected boolean addOptions(StringBuilder ret, String separator, String... strs)
        {
            for (String str : strs)
            {
                if (str != null && str.length() > 0)
                {
                    ret.append(separator);
                    ret.append(str);
                    return true;
                }
            }
            return false;
        }

        /**
         * Checks if the specified tag {@code tag} exists in the parsed
         * configuration.
         *
         * @param attr the attribute to be checked for existence.
         * @return true if it exists, false otherwise.
         */
        boolean hasDefinition(String tag)
        {
            return (tags.get(tag) != null && tags.get(tag).length() > 0);
        }

        @Override
        public String toString()
        {
            StringBuilder sb = new StringBuilder(80);
            sb.append("task:");
            for (String directive : tags.keySet())
            {
                sb.append(NEWLINE);
                sb.append("  ");
                sb.append(directive);
                sb.append(" => ");
                sb.append(tags.get(directive));
            }
            return sb.toString();
        }
    }

    /**
     * Translation task
     */
    private class Translator extends Task
    {
        Translator()
        {
            super();
        }

        Translator(Node node)
        {
            super(node);
            tags.put("name", "cetus");
        }

        @Override
        void prepareFiles()
        {
            super.prepareFiles();
            StringBuilder sb = new StringBuilder(80);
            addOptions(sb, "", "-outdir=" + info.get("dir") + FILESEP);
            addOptions(sb, "", tags.get("out"), "src-cetus");
            if (tags.get("flags") != null)
                addOptions(sb, " ", tags.get("flags").replaceAll(NEWLINE, " "));
            for (File c_file : dir.listFiles(new RegexFilter("*.c")))
                addOptions(sb, " ", c_file.getPath());
            command = sb.toString().trim();
        }

        @Override
        void invokeCommand(PrintStream out, PrintStream err)
        {
            OptionDriver driver = new OptionDriver(dir.getPath(), getChildWith(task_root, "options"));
            System.setOut(out);
            System.setErr(err);
            driver.run(command.split("[ ]+"));
            System.setOut(SYSOUT);
            System.setErr(SYSERR);
        }
    }

}
