import java.io.*;
import java.lang.reflect.Method;
import java.util.*;

import cetus.hir.*;
import cetus.exec.*;
import cetus.analysis.*;

public class LLVMCodeGenPass extends cetus.analysis.AnalysisPass
{
    int errors;
    protected static final int verbosity = PrintTools.getVerbosity();

    protected LLVMCodeGenPass(Program program)
    {
	super(program);
    }

    public String getPassName() { return new String("[LLVMCodeGenPass]"); }
                
    public void start()
    {
	PrintWriter w = new PrintWriter(System.out);
	// Transform the program here
	if(verbosity>0)
	{
	    DepthFirstIterator dfs_iter = new DepthFirstIterator(program);
	    while (dfs_iter.hasNext()) {
		
		Object o = dfs_iter.next();
		if (o instanceof Declaration) {
		    Declaration D = (Declaration) o;
		    D.print(w);
		} 
	    }
	    // dump whatever you want
	}
	w.flush();
    }       
}
