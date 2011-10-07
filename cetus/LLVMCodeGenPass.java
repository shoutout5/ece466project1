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
	
	/*try
	{
	    PrintWriter myWriter = new PrintWriter(new FileWriter("out"));
	}
	catch(IOException)
	{
	}*/

	// Transform the program here
    	
    DepthFirstIterator iter = new DepthFirstIterator(program);
   
    //Examining the file and breaking it down into parts
    
    while(iter.hasNext())
    {
        Object o = iter.next();             //get object
        
        if(o instanceof VariableDeclaration)    //global variable declarations
        {
            dump.println("Var Dec found");
            globalVariable((VariableDeclaration) o);
        }
        else if(o instanceof Procedure){
            procedure((Procedure) o);
        	
        }
        else if (o instanceof Expression){
        	Expression ex  = (Expression) o;
        	if(ex instanceof AssignmentExpression)
        		assignment((AssignmentExpression) ex);
        }
        else if(o instanceof Statement){
        	Statement currentStatement = (Statement) o;
        	
        	if(currentStatement instanceof IfStatement)
        		ifStatement((IfStatement) currentStatement);
        	
        	else if(currentStatement instanceof ForLoop)
        		forLoop((ForLoop) currentStatement); 
        	else if(currentStatement instanceof WhileLoop)
        		whileLoop((WhileLoop) currentStatement);
        	else if(currentStatement instanceof DoLoop)
        		doLoop((DoLoop) currentStatement);
        }
 
        else {
        	
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
	//code.flush();
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

            //check for possbile initializer
            try {
            Initializer init = dec.getInitializer();
            dump.println("Value Init");
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
            
            catch(ClassCastException e) {
            	System.out.println("Exception finding Global Variables");
            }        
            
        }
    }    
    private void ifStatement(IfStatement myIf){
    	dump.println("Found if statement");
		Expression terms = myIf.getControlExpression();
		//Todo - add code output here!
		dump.println("If conditions: "+terms.toString()+"\n");
		
		Statement elseStmt = myIf.getThenStatement();
		//Todo - add output to code here
		dump.println("Then statement: "+elseStmt.toString()+"\n");
    }
    private void forLoop(ForLoop fl){
    	dump.println("For loop found");  
    	Expression 	condi = fl.getCondition();
    	Statement iStmnt = fl.getInitialStatement();
    	Expression step = fl.getStep();
    	dump.println("For loop conditions: "+condi+"\n");
    	dump.println("For loop initial statement: "+iStmnt.toString());
    	dump.println("For loop step: "+step+"\n");
    }
    private void whileLoop(WhileLoop wl){
    	dump.println("While loop found");
    	Expression lc = wl.getCondition();
    	dump.println("While loop conditions:"+lc);
    	
    }
    private void doLoop(DoLoop dl){
    	dump.println("Do loop found");
    	Expression lc = dl.getCondition();
    	dump.println("Do loop conditions:"+lc);
    }
    private void assignment(AssignmentExpression ex){
    	AssignmentOperator op = ex.getOperator();
    	dump.println("Assignment op: "+op.toString());
    }
    private void procedure(Procedure proc)
    {
    	IDExpression id = proc.getName();
    	List ll = proc.getReturnType();
    	dump.println("Return type is "+ll.get(0));
    	//List l2 = proc.getParameters();
    	//dump.println("Parameters"+l2.get(0));
    	dump.println("The name of this function is "+id.getName());
    	CompoundStatement cs = proc.getBody();
    	dump.println("There are "+cs.countStatements()+" statements in this function.");
    }  
}