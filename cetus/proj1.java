import cetus.analysis.*;
import cetus.hir.*;
import cetus.transforms.*;

import java.io.*;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;

public class proj1 extends cetus.exec.Driver
{
  // ...

    public static String outputFilename;

    public void runPasses()
    {
	System.out.println("Running Proj1 driver.");
	
	(new LLVMCodeGenPass(program)).start();
    }

    public static void main(String[] args)
    {	    
	(new proj1()).run(args);
    }

    public void run(String[] args)
    {

	options.add(options.UTILITY, "output-file","out.ll","filename in which to write LLVM IR");
	
	int i; /* used after loop; don't put inside for loop */
	for (i = 0; i < args.length; ++i)
	{
	    String opt = args[i];
	    // options start with "-"

	    if (opt.charAt(0) != '-')
		/* not an option -- skip to handling options and filenames */
		break;
	    
	    int eq = opt.indexOf('=');
	    
	    // if value is not set
	    if (eq != -1)
	    {
		String option_name = opt.substring(1, eq);	       
		if (options.contains(option_name)) {
		    outputFilename = opt.substring(eq+1);
		}
	    }
	}

	parseCommandLine(args);
	
	parseFiles();
	
	if (getOptionValue("parse-only") != null)
	{
	    System.err.println("parsing finished and parse-only option set");
	    Tools.exit(0);
	}

	runPasses();
    }

  /**
   * Prints the list of options that Cetus accepts.
   */
  public void printUsage()
  {
      String usage = "\njava [-cp classpath] proj1 [option]... [file]...\n";
      usage += "\t-verbosity=[1-4]\tSet verbosity level. \n";
      usage += "\t-output-file=<name>\tSet output file name (default=out.ll). \n";
      System.err.println(usage);
  }

}
