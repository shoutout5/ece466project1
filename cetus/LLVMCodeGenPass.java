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

    String initVal;
	PrintWriter dump = new PrintWriter(System.out);     //debug dump output
	PrintWriter code = new PrintWriter(System.out);     //code output
	/*try
	{
	    PrintWriter myWriter = new PrintWriter(new FileWriter("out"));
	}
	catch(IOException)
	{
	}*/
	
	// Transform the program here
    DepthFirstIterator iter = new DepthFirstIterator(program);

    while(iter.hasNext())
    {
        Object o = iter.next();             //get object
        if(o instanceof Declaration)        //check if Declaration object
        {
            if(o instanceof VariableDeclaration)    //global variable declarations
            {
                dump.println("Var Dec found");
                VariableDeclaration varDec = (VariableDeclaration) o;

                //work on all declarations in statement if more than one declared on a line
                for(int i = 0; i < varDec.getNumDeclarators(); i++)
                {
                    Declarator dec = varDec.getDeclarator(i);
                    IDExpression id = dec.getID();
                    dump.println("Var ID: " + id.getName());

                    //check for possbile initializer
                    Initializer init = dec.getInitializer();
                    
                    if(init == null)
                        initVal = "0";
                    else
                    {
                        dump.println("Value Init");
                        initVal = init.toString();
                        initVal = initVal.substring(initVal.indexOf("=")+2,initVal.length());
                    }
                    

                    //print global var declaration code
                    code.println("@"+id.getName()+" common global i32 " + initVal);
                }
            }
        }
    }

	DepthFirstIterator dfs_iter1 = new DepthFirstIterator(program);
    while (dfs_iter1.hasNext()) {
	
	Object line = dfs_iter1.next();
	if (line instanceof Declaration) {
	    Declaration dec = (Declaration) line;
	    if(dec instanceof Procedure){
	    	Procedure proc = (Procedure) dec;	
	    	IDExpression id = proc.getName();
	    	List ll = proc.getReturnType();
	    	dump.println("Return type is "+ll.get(0));
	    /*	for(int i=0; i<ll.size(); i++)
	    	{
	    		 System.out.println(ll.get(i)+" num="+i);
	    		
	    	}
	    	*/
	    	dump.println("The name of this function is "+id.getName());
	    	CompoundStatement cs = proc.getBody();
	    	dump.println("There are "+cs.countStatements()+" statements in this function.");
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
		    //D.print(w);
		} 
	    }
	    // dump whatever you want
	}
	//w.flush();

    //print all dump and code to screen at end
	System.out.println("Dump Ouput:");
	dump.flush();
	System.out.println("\n\nCode Output:\n");
	code.flush();
    }       
}
