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
	boolean inFunction;
	PrintWriter dump = new PrintWriter(System.out);     //debug dump output
	PrintWriter code = new PrintWriter(System.out);     //code output
	PrintWriter debug = new PrintWriter(System.out);

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
		inFunction = false;
		while(iter.hasNext())
		{
			Object o = iter.next();             //get object
			//code.println("\n___________Object"+o.getClass());
			if(o instanceof VariableDeclaration)    //global variable declarations
			{
				dump.println("Var Dec found");
				declareVariable((VariableDeclaration) o);
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
		code.flush();
		System.out.println("\n\nDebug Output:\n");
		debug.flush();
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

			//check for possable initializer
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
				if(inFunction)
					code.println("%"+id.getName()+"= i32 "+ initVal);
				else{
					code.println("@"+id.getName()+" common global i32 " + initVal);
				}
			}  

			catch(ClassCastException e) {
				System.out.println("Exception finding Global Variables");
			}        

		}
		code.println();
	}    
	private void ifStatement(IfStatement myIf){
		dump.println("Found if statement");
		Expression terms = myIf.getControlExpression();
		dump.println("If conditions: "+terms.toString()+"\n");
		Statement elseStmt = myIf.getThenStatement();
		dump.println("then statement: "+elseStmt.toString()+"\n");

		//generate code
		if(terms instanceof BinaryExpression)
		{
			BinaryExpression exp = (BinaryExpression) terms;
			int LHSreg = 0;
			int RHSreg = 0;
			
			//generate proper registers of values to compare
			Expression LHS = exp.getLHS();
			Expression RHS = exp.getRHS();
			//gen LHS register if needed
			if(LHS instanceof BinaryExpression)
				LHSreg = genExpressionCode((BinaryExpression) LHS);
			else if(LHS instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)LHS).getName());
				LHSreg = ssaReg-1;
			}
			//gen RHS register if needed
			if(RHS instanceof BinaryExpression)
				RHSreg = genExpressionCode((BinaryExpression) RHS);
			else if(RHS instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				RHSreg = ssaReg-1;
			}

			
			code.print("%"+ ssaReg++ + " = icmp ");		//first part of compare expression
			//generate type of comparison
			if(exp.getOperator().toString().trim().equals("<")) code.print("slt ");
			else if(exp.getOperator().toString().trim().equals(">")) code.print("sgt ");
			else if(exp.getOperator().toString().trim().equals(">=")) code.print("sge ");
			else if(exp.getOperator().toString().trim().equals("<=")) code.print("sle ");
			else if(exp.getOperator().toString().trim().equals("==")) code.print("eq ");
			else if(exp.getOperator().toString().trim().equals("!=")) code.print("ne ");

			
			code.print("i32 ");    //+exp.getLHS()+", "+exp.getRHS());
			if(LHS instanceof IntegerLiteral)
				code.print(((IntegerLiteral) LHS).getValue() + ", ");
			else
				code.print("%" + LHSreg + ", ");
			
			if(RHS instanceof IntegerLiteral)
				code.println(((IntegerLiteral) RHS).getValue());
			else
				code.println("%" + RHSreg);

			code.println("br i1 %"+(ssaReg-1)+", label %ifLabel"+ ifLabel++ +", label %ifLabel"+ ifLabel++);
			code.println("ifLabel"+(ifLabel-2)+":");		//label for true condition

			//gen code for true condition
			FlatIterator ifIter = new FlatIterator(myIf.getThenStatement());
			while(ifIter.hasNext())
				genCode(ifIter.next());

			//gen code for false condition
			if(myIf.getElseStatement() != null)
			{
				code.println("br label %ifLabel"+ ifLabel++);	// branch to outside of whole statement

				code.println("ifLabel"+(ifLabel-2)+":");		//false label condiditon
				ifIter = new FlatIterator(myIf.getElseStatement());
				while(ifIter.hasNext())
					genCode(ifIter.next());
			}
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
			code.println("loop"+loopLabel++ +":");
			
			int LHSreg = 0;
			int RHSreg = 0;
			
			//generate proper registers of values to compare
			Expression LHS = exp.getLHS();
			Expression RHS = exp.getRHS();
			//gen LHS register if needed
			if(LHS instanceof BinaryExpression)
				LHSreg = genExpressionCode((BinaryExpression) LHS);
			else if(LHS instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)LHS).getName());
				LHSreg = ssaReg-1;
			}
			//gen RHS register if needed
			if(RHS instanceof BinaryExpression)
				RHSreg = genExpressionCode((BinaryExpression) RHS);
			else if(RHS instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				RHSreg = ssaReg-1;
			}

			//generate comparison statement
			code.print("%"+ ssaReg++ + " = icmp ");		//first part of compare expression
			//generate type of comparison
			if(exp.getOperator().toString().trim().equals("<")) code.print("slt ");
			else if(exp.getOperator().toString().trim().equals(">")) code.print("sgt ");
			else if(exp.getOperator().toString().trim().equals(">=")) code.print("sge ");
			else if(exp.getOperator().toString().trim().equals("<=")) code.print("sle ");
			else if(exp.getOperator().toString().trim().equals("==")) code.print("eq ");
			else if(exp.getOperator().toString().trim().equals("!=")) code.print("ne ");

			//generate comparison instruction
			code.print("i32 ");      //+exp.getLHS()+", "+exp.getRHS());
			
			if(LHS instanceof IntegerLiteral)
				code.print(((IntegerLiteral) LHS).getValue() + ", ");
			else
				code.print("%" + LHSreg + ", ");
			
			if(RHS instanceof IntegerLiteral)
				code.println(((IntegerLiteral) RHS).getValue());
			else
				code.println("%" + RHSreg);

			//generate branch statement
			code.println("br i1 %"+(ssaReg-1)+", label %loop"+ loopLabel++ +", label %loop"+ loopLabel++);
			//generate true label
			code.println("loop"+(loopLabel-2)+":");
			//generate loop body
			FlatIterator whileIter = new FlatIterator(wl.getBody());
			while(whileIter.hasNext())
				genCode(whileIter.next());

			//generate unconditional branch to start of loop and comparison
			code.println("br label %loop"+ (loopLabel-3));

			//generate end label
			code.println("loop"+(loopLabel-1) +":");
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
		//dump.println("There are "+cs.countStatements()+" statements in this function.");

		inFunction = true;

		//create code
		if (!(proc.getParameters().isEmpty() || proc.getParameter(0).toString().equals("void ")))
		{
			if (proc.getParameter(0).toString().startsWith("int"))
				argBuff.append("i32");
			for (int i = 1; i < proc.getParameters().size(); i++ ) {
				argBuff.append(", ");
				if (proc.getParameter(i).toString().startsWith("int"))
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

		inFunction = false;

		return false;
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
		//debug.println("\n___________Object"+o.getClass());
		if(o instanceof VariableDeclaration)    //global variable declarations
		{
			dump.println("Var Dec found");
			declareVariable((VariableDeclaration) o);
		}
		else if(o instanceof Procedure){
			procedure((Procedure) o);

		}
		else if (o instanceof ExpressionStatement){
			Expression exp = ((ExpressionStatement)o).getExpression();
			if(exp instanceof AssignmentExpression)
			assignmentExpression((AssignmentExpression) exp);
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
	
	private void assignmentExpression(AssignmentExpression assn)
	{
		Identifier var = (Identifier)assn.getLHS();
		Expression RHS = assn.getRHS();
		
		if(RHS instanceof BinaryExpression)
		{
			code.println("store i32 %" + genExpressionCode((BinaryExpression) RHS) + 
					", i32* %" + var.getName());
			
		}
		else if(RHS instanceof Identifier)
		{
			code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
			code.println("store i32 %"+ (ssaReg-1) + ", i32* %"+var.getName());
		}
		else if(RHS instanceof IntegerLiteral)
		{
			code.println("store i32 "+ ((IntegerLiteral)RHS).getValue() +
					", i32* %"+var.getName());
		}
	}
	
	private int genExpressionCode(BinaryExpression exp)
	{
		BinaryOperator operator = exp.getOperator();	//get operator
		Expression LHS = exp.getLHS();					//get left hand side
		Expression RHS = exp.getRHS();					//get right hand side
		
		int resultReg = ssaReg++;						//register to put result in
		
		StringBuffer instrBuff = new StringBuffer("");	//buffer for output to be written upon completion
		StringBuffer setupInstr = new StringBuffer(""); //buffer for extra load instructions
		
		instrBuff = instrBuff.append("%" + resultReg + " = ");	//print start of instruction
		
		//decide on function to be used
		if(exp.getOperator().toString().trim().equals("+")) 
			instrBuff = instrBuff.append("add i32 ");
		else if(exp.getOperator().toString().trim().equals("-"))
			instrBuff = instrBuff.append("sub i32 ");
		else if(exp.getOperator().toString().trim().equals("*"))
			instrBuff = instrBuff.append("mul i32 ");
		else if(exp.getOperator().toString().trim().equals("/"))
			instrBuff = instrBuff.append("sdiv i32 ");
		
		//generate code and result registers for left hand size
		if(LHS instanceof IntegerLiteral)
			instrBuff = instrBuff.append(((IntegerLiteral)LHS).getValue());
		else if(LHS instanceof BinaryExpression)
			instrBuff = instrBuff.append("%" + genExpressionCode((BinaryExpression)LHS));
		else if(LHS instanceof Identifier)
		{
			//load from memory into a register
			setupInstr = setupInstr.append("%" + ssaReg++ + " = load i32* %" +
					((Identifier)LHS).getName() + "\n");
			instrBuff = instrBuff.append(", %" + (ssaReg-1));
		}
		
		//generate code and result registers for right hand size
		if(RHS instanceof IntegerLiteral)
			instrBuff = instrBuff.append(", " + ((IntegerLiteral)RHS).getValue());
		else if(RHS instanceof BinaryExpression)
			instrBuff = instrBuff.append(", %" + genExpressionCode((BinaryExpression)RHS));
		else if(RHS instanceof Identifier)
		{
			//load from memory into a register
			setupInstr = setupInstr.append("%" + ssaReg++ + " = load i32* %" +
					((Identifier)RHS).getName() + "\n");
			instrBuff = instrBuff.append(", %" + (ssaReg-1));
		}
			
		if(!setupInstr.toString().equals(""))		//print load instructions if required
			code.print(setupInstr);
		
		code.println(instrBuff);
		
		return resultReg;
	}
}