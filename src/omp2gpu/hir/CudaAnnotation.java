package omp2gpu.hir;

import java.util.*;
import cetus.hir.*;
public class CudaAnnotation extends PragmaAnnotation
{
	// Pragmas used without values
	private static final Set<String> no_values =
		new HashSet<String>(Arrays.asList("ainfo", "cpurun", "gpurun", 
				"noploopswap", "noloopcollapse", "nogpurun"));

	// Pragmas used with collection of values
	private static final Set<String> collection_values =
		new HashSet<String>(Arrays.asList("c2gmemtr", "noc2gmemtr", "g2cmemtr",
		"nog2cmemtr", "registerRO", "registerRW", "sharedRO", "sharedRW", 
		"texture", "constant", "noconstant", "maxnumofblocks", "noreductionunroll",
		"nocudamalloc", "nocudafree", "cudafree", "procname", "kernelid",
		"noregister", "noshared", "notexture", "threadblocksize", "enclosingloops",
		"multisrccg", "multisrcgc", "conditionalsrc"));

	/**
	 * Constructs an empty omp annotation.
	 */
	public CudaAnnotation()
	{
		super();
	}

	/**
	 * Constructs an omp annotation with the given key-value pair.
	 */
	public CudaAnnotation(String key, Object value)
	{
		super();
		put(key, value);
	}

	/**
	 * Returns the string representation of this cuda annotation.
	 * @return the string representation.
	 */
	public String toString()
	{
		if ( skip_print )
			return "";

		StringBuilder str = new StringBuilder(80);

		str.append(super.toString()+"cuda ");

		// Process "ainfo", "gpurun", or "cpurun" before any other keys are processed.
		if ( containsKey("ainfo") )
			str.append("ainfo ");
		if ( containsKey("gpurun") )
			str.append("gpurun ");
		if ( containsKey("cpurun") )
			str.append("cpurun ");
		if ( containsKey("nogpurun") )
			str.append("nogpurun ");

		for ( String key : keySet() )
		{
			if ( key.equals("gpurun") || key.equals("cpurun")
					|| key.equals("ainfo") || key.equals("nogpurun") )
				;
			else if ( no_values.contains(key) )
				str.append(key+" ");
			else if ( collection_values.contains(key) )
			{
				Object value = get(key);
				if ( value instanceof Collection )
					str.append(key+"("+
						PrintTools.collectionToString((Collection)value, ", ")+") ");
				else // e.g., schedule
					str.append(key+"("+value+") ");
			}
			else
			{
				str.append(key+" ");
				if ( get(key) != null )
					str.append(get(key)+" ");
			}
		}

		return str.toString();
	}
}
