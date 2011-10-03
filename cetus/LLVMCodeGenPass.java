import java.io.*;
import java.lang.reflect.Method;
import java.util.*;

import cetus.hir.*;
import cetus.exec.*;
import cetus.analysis.*;

public class LLVMCodeGenPass extends cetus.analysis.AnalysisPass
{
	int errors;
	PrintWriter dump = new PrintWriter(System.out);     //debug dump output
	PrintWriter code = new PrintWriter(System.out);     //code output

	protected static final int verbosity = PrintTools.getVerbosity();

	protected LLVMCodeGenPass(Program program) 
	{
		super(program);
	}

	public String getPassName() { return new String("[LLVMCodeGenPass]"); }

	public void start()
	{
		// Transform the program here
		DepthFirstIterator iter = new DepthFirstIterator(program);

		//look for global variable declarations
		while(iter.hasNext())
		{
			Object o = iter.next();             //get object
			
			if(o instanceof VariableDeclaration)    //global variable declarations
			{
				if((((VariableDeclaration) o).getParent()) instanceof TranslationUnit)
				{
					dump.println("Global Var Dec found");
					globalVariable((VariableDeclaration) o);
				}
			}
		}

		iter = new DepthFirstIterator(program);     //reset iterator
		code.println("");
		
		//look for procedure declarations
		while (iter.hasNext()) {

			Object line = iter.next();

			if(line instanceof Procedure){
				procedure((Procedure) line);

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

	private void globalVariable(VariableDeclaration varDec)
	{
		String initVal;

		//work on all declarations in statement if more than one declared on a line
		for(int i = 0; i < varDec.getNumDeclarators(); i++)
		{
			Declarator dec = varDec.getDeclarator(i);
			IDExpression id = dec.getID();
			dump.println("Var ID: " + id.getName());
			//dump.println("Parent: " + varDec.getParent() + "\n");

			//check for possible initializer
			Initializer init = dec.getInitializer();

			if (init != null)
			{
				dump.println("Value Init");
				initVal = init.toString();
				initVal = initVal.substring(initVal.indexOf("=")+2,initVal.length());
				
				//print global var declaration code
				code.println("@"+id.getName()+" global i32 " + initVal);
			}
			else
				code.println("@"+id.getName()+" common global i32 0");		
		}
	}    

	private void procedure(Procedure proc)
	{
		String returnType;
		StringBuffer argBuff = new StringBuffer("");
		dump.println("Return type is " + proc.getReturnType());
		/*	for(int i=0; i<ll.size(); i++)
    	{
    		 System.out.println(ll.get(i)+" num="+i);

    	}
		 */
		
		System.out.println("Parameters: " + proc.getParameters());
		
		if (proc.getReturnType().toString().equals("[int]"))
				returnType = "i32";
		else returnType = "test";	// TO BE IMPLEMENTED
		
		if (!(proc.getParameters().isEmpty() || proc.getParameter(0).toString().equals("void ")))
		{
			if (proc.getParameter(0).toString().startsWith("int"))
				argBuff.append("i32");
			for (int i = 1; i < proc.getParameters().size(); i++ ) {
				argBuff.append(", ");
				if (proc.getParameter(i).toString().startsWith("int)"))
						argBuff.append("i32");
				argBuff.append("i32");
					//{arguments, ", ", proc.getParameter(i).toString()};
			}
			//System.out.println("Arguments: " + argBuff);
		}
		
		dump.println("The name of this function is "+proc.getName());
		dump.println("There are "+proc.getBody().countStatements()+" statements in this function.");

		code.println("define " +returnType + " @" + proc.getName() + "(" + argBuff + ") " + "{");
		code.println("}\n");
	}  
}