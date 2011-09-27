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

	DepthFirstIterator dfs_iter1 = new DepthFirstIterator(program);
    while (dfs_iter1.hasNext()) {
	
	Object line = dfs_iter1.next();
	if (line instanceof Declaration) {
	    Declaration dec = (Declaration) line;
	    if(dec instanceof Procedure){
	    	Procedure proc = (Procedure) dec;	
	    	IDExpression id = proc.getName();
	    	System.out.println(id.getName());
	    	for(int i = 0; i<proc.getNumParameters(); i++){
	    		System.out.println(" "+proc.getParameter(i)+" ");
	    	}
	    }
	 }
    }

	if(verbosity>0)
	{
	    DepthFirstIterator dfs_iter = new DepthFirstIterator(program);
	    while (dfs_iter.hasNext()) {
		
		Object o = dfs_iter.next();
		if (o instanceof Declaration) {
		    Declaration D = (Declaration) o;
		    if(D instanceof Procedure){
		    	
		    }
		    D.print(w);
		} 
	    }
	    // dump whatever you want
	}
	w.flush();
    }       
}
