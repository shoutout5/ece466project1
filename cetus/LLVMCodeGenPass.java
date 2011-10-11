import java.io.*;
import java.lang.reflect.Method;
import java.util.*;

import cetus.hir.*;
import cetus.exec.*;
import cetus.analysis.*;

public class LLVMCodeGenPass extends cetus.analysis.AnalysisPass
{
	int errors;
	int currentRetVal = 0;
	int ssaReg = 0;
	int ifLabel = 0;
	int loopLabel = 0;
	//boolean inFunction;
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

		FlatIterator iter = new FlatIterator(program);		//get translation unit
		iter = new FlatIterator(iter.next());				//iterate on top level of program ie.
		//global vars and procedures

		//Examining the file and breaking it down into parts
		//inFunction = false;
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

		iter.reset();

		code.println("");

		while(iter.hasNext())
		{
			Object o = iter.next();             //get object
			//code.println("\n___________Object"+o.getClass());
			/*if(o instanceof VariableDeclaration)    //global variable declarations
        {
            dump.println("Var Dec found");
            declareVariable((VariableDeclaration) o);
        }
        else */if(o instanceof Procedure){
        	procedure((Procedure) o);	
        }
        /*else if (o instanceof Expression){
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
        	else if(currentStatement instanceof ReturnStatement)
        		inFunction = foundReturn((ReturnStatement) currentStatement);
        }

        else {

        }*/
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

	private void declareVariable(VariableDeclaration varDec)
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
				//local vs global variable declarations
				/*if(inFunction)
            	 code.println("%"+id.getName()+"= i32 "+ initVal);
             else{
            	 code.println("@"+id.getName()+" common global i32 " + initVal);
             }*/
				code.println("%" + id.getName() + " = alloca i32");
				code.println("store i32 " + initVal + ", i32* %" + id.getName());
			}  

			catch(ClassCastException e) {
				System.out.println("Exception finding local Variables");
			}        

		}
		code.println();
	}    
	private void ifStatement(IfStatement myIf){
		dump.println("Found if statement");
		Expression terms = myIf.getControlExpression();
		dump.println("If conditions: "+terms.toString()+"\n");
		Statement elseStmt = myIf.getThenStatement();
		dump.println("Then statement: "+elseStmt.toString()+"\n");

		//generate code
		if(terms instanceof BinaryExpression)
		{
			BinaryExpression exp = (BinaryExpression) terms;

			code.print("%"+ ssaReg++ + " = icmp ");		//first part of compare expression
			//generate type of comparison
			if(exp.getOperator().toString().trim().equals("<")) code.print("slt ");
			else if(exp.getOperator().toString().trim().equals(">")) code.print("sgt ");
			else if(exp.getOperator().toString().trim().equals(">=")) code.print("sge ");
			else if(exp.getOperator().toString().trim().equals("<=")) code.print("sle ");
			else if(exp.getOperator().toString().trim().equals("==")) code.print("eq ");
			else if(exp.getOperator().toString().trim().equals("!=")) code.print("ne ");

			//TODO- generate proper registers of values to compare
			code.println("i32 "+exp.getLHS()+", "+exp.getRHS());

			code.println("br i1 %"+(ssaReg-1)+", label %ifLabel"+ ifLabel++ +", label %ifLabel"+ ifLabel++);
			code.println("ifLabel"+(ifLabel-2)+":");		//label for true condition

			//gen code for true condition
			FlatIterator ifIter = new FlatIterator(myIf.getThenStatement());
			while(ifIter.hasNext())
				genCode(ifIter.next());

			code.println("br label %ifLabel"+ ifLabel++);	// branch to outside of whole statement

			//gen code for false condition
			code.println("ifLabel"+(ifLabel-2)+":");		//false label condiditon
			ifIter = new FlatIterator(myIf.getElseStatement());
			while(ifIter.hasNext())
				genCode(ifIter.next());

			code.println("ifLabel"+(ifLabel-1)+":");		//label for rest of code

		} else {code.println("ERROR: Unhandeled if statement condition not binary expression");}
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

		if(lc instanceof BinaryExpression)
		{
			BinaryExpression exp = (BinaryExpression) lc;

			//generate top of loop label
			code.print("loop"+loopLabel++ +":");

			//generate comparison statement
			code.print("%"+ ssaReg++ + " = icmp ");		//first part of compare expression
			//generate type of comparison
			if(exp.getOperator().toString().trim().equals("<")) code.print("slt ");
			else if(exp.getOperator().toString().trim().equals(">")) code.print("sgt ");
			else if(exp.getOperator().toString().trim().equals(">=")) code.print("sge ");
			else if(exp.getOperator().toString().trim().equals("<=")) code.print("sle ");
			else if(exp.getOperator().toString().trim().equals("==")) code.print("eq ");
			else if(exp.getOperator().toString().trim().equals("!=")) code.print("ne ");

			//TODO- generate proper registers of values to compare
			code.println("i32 "+exp.getLHS()+", "+exp.getRHS());

			//generate branch statement
			code.println("br i1 %"+(ssaReg-1)+", label %loop"+ loopLabel++ +", label %loop"+ loopLabel++);

			//generate loop body
			FlatIterator whileIter = new FlatIterator(wl.getBody());
			while(whileIter.hasNext())
				genCode(whileIter.next());

			//generate unconditional branch to start of loop and comparison

			//generate end label
			code.print("loop"+loopLabel++ +":");
		} 
		else{code.println("_________ERROR: binray expressions only handled for while loop");}
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
	private boolean procedure(Procedure proc)
	{
		StringBuffer argBuff = new StringBuffer("");
		FlatIterator procIter = new FlatIterator(proc.getBody());		//set up iterator on body of procedure
		IDExpression id = proc.getName();
		List ll = proc.getReturnType();
		dump.println("Return type is "+ll.get(0));
		//List l2 = proc.getParameters();
		//dump.println("Parameters"+l2.get(0));
		dump.println("The name of this function is "+id.getName());
		CompoundStatement cs = proc.getBody();
		dump.println("There are "+cs.countStatements()+" statements in this function.");

		//create code
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

		String retType = ll.get(0).toString();
		code.print("define ");
		if(retType.equals("int"))
			code.print("i32 ");
		else
			code.print("void ");

		code.print("@"+id.getName()+"("+argBuff+") ");
		code.println("nounwind ssp{");
		code.println("entry_"+id.getName()+":");
		if(retType.equals("int"))
			code.println("%retval"+currentRetVal++ + " = alloca i32");

		while(procIter.hasNext())		//iterate on body of procedure
		{
			genCode(procIter.next());             //get statements and generate code   
		}

		code.println("}\n");

		return true;
	}  
	private boolean foundReturn(ReturnStatement rs){
		Expression ex = rs.getExpression();
		dump.println("Return value: "+ex);

		//print code
		code.println("%"+ ssaReg++ +" = "+ex.toString());
		code.println("store i32 %"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
		code.println("return_"+currentRetVal+":");
		code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
		code.println("ret i32 %retval"+(currentRetVal-1));
		return false;
	}

	private void genCode(Object o){
		//code.println("\n___________Object"+o.getClass());
		//System.out.println("Class " + o.getClass());
		if(o instanceof DeclarationStatement)
		{
			DeclarationStatement decStmt = (DeclarationStatement) o;
			if(decStmt.getDeclaration() instanceof VariableDeclaration)    //local variable declarations
			{
				dump.println("Local Var Dec found");
				declareVariable((VariableDeclaration) decStmt.getDeclaration());
			}
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
			else if(currentStatement instanceof ReturnStatement)
				foundReturn((ReturnStatement) currentStatement);
		}
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
}