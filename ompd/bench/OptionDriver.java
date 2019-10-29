package bench;

import cetus.exec.*;
import cetus.hir.*;
import cetus.transforms.*;

import java.io.*;
import java.util.*;

import org.w3c.dom.*;

/**
 * This driver takes cetus options from an XML document which can carry more
 * information/control than the standard command-line options.
 */
public class OptionDriver extends Driver
{
    /**
     * Constants
     */
    private static final String LISTSEP = "[;" + System.getProperty("line.separator") + "]+";

    /**
     * The working directory
     */
    private String pwd;

    /**
     * The configuration document
     */
    private Node cfg;

    /**
     * Constructor
     */
    public OptionDriver()
    {
        super();
    }

    /**
     * Constructs a new option driver with the specified working directory and
     * configuration node that defines options.
     *
     * @param pwd the working directory for the translator.
     * @param cfg the XML document that defines extra options.
     */
    public OptionDriver(String pwd, Node cfg)
    {
        super();
        this.pwd = pwd;
        this.cfg = cfg;
    }

    /**
     * Runs cetus with the specified arguments and configuration document.
     *
     * @param args the list of command-line arguments.
     */
    @Override
    public void run(String[] args)
    {
        parseCommandLine(args);
        // Invokes xml option parser.
        parseOptions();
        parseFiles();
        runPasses();
        PrintTools.printlnStatus("Printing...", 1);
        try
        {
            program.print();
        }
        catch (IOException e)
        {
            System.err.println("could not write output files: " + e);
            System.exit(1);
        }
    }

    /**
     * Parses files after creating a new parser having the specified working
     * directory. This method was overridden to construct a parser with a custom
     * starting directory. The original driver does not allow execution of
     * preprocessor other than the JAVA runtime's current directory, so it is
     * impossible to launch the preprocessor without replacing all the directory
     * shortcuts such as '.' and '..' from a different working directory.
     */
    @Override
    protected void parseFiles()
    {
        try
        {
            program = new Program();
            Parser parser = new Parser(pwd);
            for (String file : filenames)
                program.addTranslationUnit(parser.parse(file));
        }
        catch (IOException ex)
        {
            System.err.println("I/O error parsing files");
            System.err.println(ex);
            System.exit(1);
        }
        catch (Exception ex)
        {
            System.err.println("Miscellaneous exception while parsing files: " + ex);
            ex.printStackTrace();
            System.exit(1);
        }
        SymbolTools.linkSymbol((Traversable) program);
        TransformPass.run(new AnnotationParser(program));
    }

    /**
     * Parses the configuration document for the driver. The configuration
     * document accepts the following format.
     * <pre>
     * <options>
     *  <option>
     *   <name>$option_name</name>
     *   <value>$option_value</value>
     *   <select hir="<$hirname>" type="<include|exclude>">$names</select>
     *  </option>
     * </options>
     * </pre>
     */
    private void parseOptions()
    {
        if (cfg == null)
            return; // null option is ignored - acts just like cetus.exec.Driver.
        else if (!cfg.getNodeName().equals("options"))
            throw new InternalError("Unknown option configuration");
        NodeList option_list = cfg.getChildNodes();
        for (int i = 0; i < option_list.getLength(); i++)
        {
            Node option_node = option_list.item(i);
            if (option_node.getNodeType() != Node.ELEMENT_NODE)
                continue;
            if (!option_node.getNodeName().equals("option"))
                throw new InternalError("Unknown option configuration");
            NodeList records = option_node.getChildNodes();
            String name = getNodeValueWith(records, "name");
            String value = getNodeValueWith(records, "value");
            if (value.length() == 0)
                value = "1";
            options.setValue(name, value);
            parseSelect(name, records);
            // TODO: more parsing option can be added, e.g., metric request.
        }
    }

    /**
     * Parses the "select" node to enable selective optimization.
     *
     * @param name    the name of the option affected.
     * @param records the node list configured for the {@code name}.
     */
    private void parseSelect(String name, NodeList records)
    {
        for (Element select : getNodesWith(records, "select"))
        {
            String hir = select.getAttribute("hir").trim();
            String type = select.getAttribute("type").trim();
            if (type.equals("include"))
            {
                for (String hir_name : select.getTextContent().trim().split(LISTSEP))
                    options.include(name, hir, hir_name.trim());
            }
            else if (type.equals("exclude"))
            {
                for (String hir_name : select.getTextContent().trim().split(LISTSEP))
                    options.exclude(name, hir, hir_name.trim());
            }
            else
                throw new InternalError("Unknown selection type");
        }
    }

    /**
     * Returns the list of child elements within the specified node list, having
     * the specified tag name.
     *
     * @param records the node list to be searched.
     * @param name    the node name to be searched for.
     * @return the list of such elements.
     */
    private static List<Element> getNodesWith(NodeList records, String name)
    {
        List<Element> ret = new LinkedList<Element>();
        for (int i = 0; i < records.getLength(); i++)
        {
            Node record_node = records.item(i);
            if (record_node.getNodeType() != Node.ELEMENT_NODE)
                continue;
            if (record_node.getNodeName().equals(name))
                ret.add((Element) record_node);
        }
        return ret;
    }

    /**
     * Returns the value of the node with the specified tag name, which appears
     * first in the specifed node list.
     *
     * @param records the node list to be searched.
     * @param name    the node name to be searched for.
     * @return the text node value of the node that was found first.
     */
    private static String getNodeValueWith(NodeList records, String name)
    {
        for (int i = 0; i < records.getLength(); i++)
        {
            Node record_node = records.item(i);
            if (record_node.getNodeType() != Node.ELEMENT_NODE)
                continue;
            if (record_node.getNodeName().equals(name))
                return record_node.getTextContent().trim();
        }
        return "";
    }
}
