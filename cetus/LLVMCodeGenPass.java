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
	PrintWriter dump = new PrintWriter(System.out);     //debug dump output
	PrintWriter code; //= new PrintWriter(System.out);     //code output
	PrintWriter debug = new PrintWriter(System.out);

	protected static final int verbosity = PrintTools.getVerbosity();

	protected LLVMCodeGenPass(Program program, String outputFilename)
	{
		super(program);
		
		try{
			code = new PrintWriter(new FileWriter(outputFilename));
		}
		catch(Exception e)
		{
			System.out.println("\n\nERROR:  unable to create output file\n");
		}
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
			if(o instanceof Procedure){
				procedure((Procedure) o);
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

		//add definitions for printf() and scanf()
		code.println("\n\n");
		code.println("declare i32 @scanf(i8*, ...)");
		code.println("declare i32 @printf(i8*, ...)");

		//print all dump and code to screen at end
		System.out.println("Dump Ouput:");
		dump.flush();
		System.out.println("Code Output:\n");
		code.flush();
		System.out.println("\n\nDebug Output:\n");
		debug.flush();
	} 

	private void declareVariable(VariableDeclaration varDec)
	{
		String initVal = new String("0");
		
		//work on all declarations in statement if more than one declared on a line
		for(int i = 0; i < varDec.getNumDeclarators(); i++)
		{
			VariableDeclarator dec = (VariableDeclarator) varDec.getDeclarator(i);
			IDExpression id = dec.getID();
			dump.println("Var ID: " + id.getName());
			String arraySize = dec.getArraySpecifiers().toString().trim();
			boolean isArray;
			boolean is2dArray;
			String arraySpec=null;

			try{
				arraySize = arraySize.substring(2,arraySize.lastIndexOf("]")-1 ).trim();
				isArray=true;
				if(arraySize.contains("]["))
					is2dArray = true;
				else
					is2dArray = false;
				if(is2dArray){
					String sizeOne = arraySize.substring(0,arraySize.indexOf("]["));
					String sizeTwo = arraySize.substring(arraySize.indexOf("][")+2);
					arraySpec= new String("[ "+sizeOne+" ["+sizeTwo+" x i32]]");
				} else {
					arraySpec= new String("["+arraySize+" x i32]");
				}
			}
			
			catch(StringIndexOutOfBoundsException e){
				isArray=false;
			}
			//check for possible initializer
			try {
				Initializer init = dec.getInitializer();
				dump.println("Value Init");
				
				//local vs global variable declarations
				/*if(inFunction)
            	 code.println("%"+id.getName()+"= i32 "+ initVal);
             else{
            	 code.println("@"+id.getName()+" common global i32 " + initVal);
             }*/
				if(isArray)
					code.println("%" + id.getName() + " = alloca "+arraySpec);
				else
				{
					code.print("%" + id.getName() + " = alloca");
					
					if (dec.getTypeSpecifiers().get(0).toString().equals("int"))
						code.print(" i32");
					
					if (dec.getTypeSpecifiers().size() == 1)
						code.println("");
					else 
					{
						for (int j = 1; j < dec.getTypeSpecifiers().size(); j++)
							code.print(dec.getTypeSpecifiers().get(j).toString().trim());
						    code.println("");
					}
				}
				if (dec.getTypeSpecifiers().size() == 1)
				{
					if(init != null)
					{
						initVal = init.toString();
						initVal = initVal.substring(initVal.indexOf("=")+2,initVal.length());
					} 
					if(!isArray)
						code.println("store i32 " + initVal + ", i32* %" + id.getName());
				}
				else // pointers
				{
					if (init != null)
					{
						code.print("store i32");
						for (int j = 1; j < dec.getTypeSpecifiers().size(); j++)
							code.print(dec.getTypeSpecifiers().get(j).toString().trim());

						initVal = init.toString();
						initVal = " %" + initVal.substring(initVal.indexOf("&")+2,initVal.length() - 1);

						code.print(initVal + ", i32");
						for (int j = 1; j < dec.getTypeSpecifiers().size(); j++)
							code.print(dec.getTypeSpecifiers().get(j).toString().trim());

						code.print("* " + "%" + id.getName());
					}
					else
						code.println("");
				}
			}  

			catch(ClassCastException e) {
				System.out.println("Exception finding local Variables");
			}        

		}
		//code.println();
	}  

	private void globalVariable(VariableDeclaration varDec)
	{
		String initVal;
			
		//work on all declarations in statement if more than one declared on a line
		for(int i = 0; i < varDec.getNumDeclarators(); i++)
		{
			boolean isArray;
			boolean is2dArray;
			String arraySpec=null;
			Declarator dec = varDec.getDeclarator(i);
			IDExpression id = dec.getID();
			dump.println("Var ID: " + id.getName());
			//dump.println("Specifiers = " + dec.getSpecifiers());
			//dump.println("Type Specifiers = " + dec.getTypeSpecifiers());
			//dump.println("Parent: " + varDec.getParent() + "\n");
			String arraySize;

			try{
				 arraySize = dec.getArraySpecifiers().toString().trim();
				arraySize = arraySize.substring(2,arraySize.lastIndexOf("]")-1 ).trim();
				isArray=true;
				if(arraySize.contains("]["))
					is2dArray = true;
				else
					is2dArray = false;
				if(is2dArray){
					String sizeOne = arraySize.substring(0,arraySize.indexOf("]["));
					String sizeTwo = arraySize.substring(arraySize.indexOf("][")+2);
					arraySpec= new String("[ "+sizeOne+" ["+sizeTwo+" x i32]]");
				} else {
					arraySpec= new String("["+arraySize+" x i32]");
				}
			}
			catch(StringIndexOutOfBoundsException e){
				isArray=false;
			}
			catch(NullPointerException e){
				isArray=false;
			}
			
			//check for possible initializer;
			Initializer init;
			try{
				init = dec.getInitializer();
			}
			catch(ClassCastException e){
				init = null;
			}
			if (dec.getSpecifiers().equals("[]"))
				dump.println("int type!");

			code.print("@"+id.getName());

			if (init == null)
				code.print(" common");

			code.print(" global");
			try{
			VariableDeclarator vdec = (VariableDeclarator) dec;
			if (vdec.getTypeSpecifiers().get(0).toString().equals("int"))
			{
				if (vdec.getTypeSpecifiers().size() == 1)
				{
					if (isArray == true)
						code.print(" i32 "+arraySpec);
					else
						code.print(" i32");
				}
				else // if (dec.getTypeSpecifiers().get(1).toString().trim().equals("*"))
				{
					if (init != null)
					{
						FlatIterator children = new FlatIterator(program);
						children = new FlatIterator(children.next());	
						initVal = init.toString();
						initVal = initVal.substring(initVal.indexOf("&")+2,initVal.length() - 1);
						//debug.println("initial Value: " + initVal);

						while (children.hasNext())
						{
							Object child = children.next();

							if(child instanceof VariableDeclaration)    //global variable declarations
							{
								if((((VariableDeclaration) child).getParent()) instanceof TranslationUnit)
								{
									for(int k = 0; k < ((VariableDeclaration) child).getNumDeclarators(); k++)
									{
										VariableDeclarator referencedDec = (VariableDeclarator) ((VariableDeclaration) child).getDeclarator(k);
										//debug.println(referencedDec.getID());
										if (referencedDec.getID().toString().equals(initVal))
										{
											//debug.println("found it! :)");
											
											boolean pointsToArray = false;
											boolean pointsTo2DArray = false;
											String pointsToArraySpec=null;
											String pointsToArraySize = referencedDec.getArraySpecifiers().toString().trim();

											try{
												pointsToArraySize = pointsToArraySize.substring(2,pointsToArraySize.lastIndexOf("]")-1 ).trim();
												pointsToArray=true;
												if(pointsToArraySize.contains("]["))
													pointsTo2DArray = true;
												else
													pointsTo2DArray = false;
												if(pointsTo2DArray){
													String sizeOne = pointsToArraySize.substring(0,pointsToArraySize.indexOf("]["));
													String sizeTwo = pointsToArraySize.substring(pointsToArraySize.indexOf("][")+2);
													pointsToArraySpec= new String("[ "+sizeOne+" ["+sizeTwo+" x i32]]");
												} else {
													pointsToArraySpec= new String("["+pointsToArraySize+" x i32]");
												}
											}
											catch(StringIndexOutOfBoundsException e){
												pointsToArray=false;
											}
											
											if (pointsToArray || pointsTo2DArray)
												code.print(" " + pointsToArraySpec);
											else
												code.print(" i32");
										}
									}
								}
							}
						}
					}
					else
					{
						code.print(" i32");
					}
				}
			}

			if (vdec.getTypeSpecifiers().size() == 1)
				code.print(" ");
			else 
			{
				for (int j = 1; j < vdec.getTypeSpecifiers().size(); j++)
					code.print(vdec.getTypeSpecifiers().get(j).toString().trim());
				code.print(" ");
			}
			if (init == null)
			{
				if (vdec.getTypeSpecifiers().size() == 1)
					code.println("");
				else 
					if (vdec.getTypeSpecifiers().get(1).toString().trim().equals("*"))
						code.println("null");
			}
			else
			{
				initVal = init.toString();
				if (vdec.getTypeSpecifiers().size() == 1)
					initVal = initVal.substring(initVal.indexOf("=")+2,initVal.length());
				else
				{
					if (vdec.getTypeSpecifiers().get(1).toString().trim().equals("*"))
						initVal = "@" + initVal.substring(initVal.indexOf("&")+2,initVal.length() - 1);						
				}
				code.println(initVal);
			}	
		}
			catch(ClassCastException e){}
	  }
	}    

	private void ifStatement(IfStatement myIf){
		dump.println("Found if statement");
		Expression terms = myIf.getControlExpression();
		dump.println("If conditions: "+terms.toString()+"\n");
		Statement elseStmt = myIf.getThenStatement();
		dump.println("then statement: "+elseStmt.toString()+"\n");

		boolean LHSIsArray = false;
		boolean LHSIs2dArray = false;
		boolean RHSIsArray = false;
		boolean RHSIs2dArray = false;
		String LHSArrayLocation = null;
		String LHSArrayLocation2 = null;
		String RHSArrayLocation = null;
		String RHSArrayLocation2 = null;
		String nameLHS = null;
		String nameRHS = null;
		
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
			else if(LHS instanceof ArrayAccess){
				String name=null;
				LHSIsArray = true;
				ArrayAccess aL = (ArrayAccess) LHS;
				nameLHS = aL.getArrayName().toString();
				LHSArrayLocation=aL.getIndices().get(0).toString();
				if(aL.getNumIndices() > 1) {
					LHSIs2dArray = true;
					LHSArrayLocation2=aL.getIndices().get(1).toString();
				}
				if(!LHSIs2dArray){
					 String nameOfArray = nameLHS;
					nameLHS = new String(nameLHS+"_"+LHSArrayLocation);
					code.println("%"+nameLHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+LHSArrayLocation);
					code.println("%"+nameLHS+" = load i32* "+nameLHS);
				}
				else if (LHSIs2dArray){
					String nameOfArray = nameLHS;
					nameLHS = new String(nameOfArray+"_"+LHSArrayLocation+"_"+LHSArrayLocation2);
					code.println("%"+nameLHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+LHSArrayLocation+", i32 "+LHSArrayLocation2);
					code.println("%"+nameLHS+" = load i32* "+nameLHS);
				}
			}
			//gen RHS register if needed
			if(RHS instanceof BinaryExpression)
				RHSreg = genExpressionCode((BinaryExpression) RHS);
			else if(RHS instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				RHSreg = ssaReg-1;
			}
			else if(RHS instanceof ArrayAccess){
				String name=null;
				RHSIsArray = true;
				ArrayAccess aL = (ArrayAccess) RHS;
				nameRHS = aL.getArrayName().toString();
				RHSArrayLocation=aL.getIndices().get(0).toString();
				if(aL.getNumIndices() > 1) {
					RHSIs2dArray = true;
					RHSArrayLocation2=aL.getIndices().get(1).toString();
				}
				if(!RHSIs2dArray){
					 String nameOfArray = nameRHS;
					nameLHS = new String(nameRHS+"_"+RHSArrayLocation);
					code.println("%"+nameRHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+RHSArrayLocation);
					code.println("%"+nameRHS+" = load i32* "+nameRHS);
				}
				else if (RHSIs2dArray){
					String nameOfArray = nameRHS;
					nameRHS = new String(nameOfArray+"_"+RHSArrayLocation+"_"+RHSArrayLocation2);
					code.println("%"+nameRHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+RHSArrayLocation+", i32 "+RHSArrayLocation2);
					code.println("%"+nameRHS+" = load i32* "+nameRHS);
				}
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
			else if(LHSIsArray)
				code.print("%"+nameLHS+", ");
			else
				code.print("%" + LHSreg + ", ");

			if(RHS instanceof IntegerLiteral)
				code.println(((IntegerLiteral) RHS).getValue());
			else if(RHSIsArray)
				code.print("%"+nameRHS+", ");
			else
				code.println("%" + RHSreg);

			code.println("br i1 %"+(ssaReg-1)+", label %ifLabel"+ ifLabel++ +", label %ifLabel"+ ifLabel++);
			code.println("ifLabel"+(ifLabel-2)+":");		//label for true condition

			//gen code for true condition
			FlatIterator ifIter = new FlatIterator(myIf.getThenStatement());
			while(ifIter.hasNext())
				genCode(ifIter.next());
			
			if(myIf.getElseStatement() == null)
				code.println("br label %ifLabel"+ (ifLabel-1));	//branch out of if statement

			//gen code for false condition
			if(myIf.getElseStatement() != null)
			{
				code.println("br label %ifLabel"+ ifLabel++);	// branch to outside of whole statement

				code.println("ifLabel"+(ifLabel-2)+":");		//false label condiditon
				ifIter = new FlatIterator(myIf.getElseStatement());
				while(ifIter.hasNext())
					genCode(ifIter.next());
				
				code.println("br label %ifLabel"+ (ifLabel-1));	//branch out of if statement
			}
			code.println("ifLabel"+(ifLabel-1)+":");		//label for rest of code

		} else {code.println("ERROR: Unhandeled if statement condition not binary expression");}
	}
	private void forLoop(ForLoop fl){
		dump.println("For loop found");  
		Expression 	lc = fl.getCondition();
		Statement iStmnt = fl.getInitialStatement();
		Expression step = fl.getStep();
		dump.println("For loop conditions: "+lc+"\n");
		dump.println("For loop initial statement: "+iStmnt.toString());
		dump.println("For loop step: "+step+"\n");

		Expression init;

		//generate initial statement to setup loop
		if(iStmnt instanceof ExpressionStatement)
		{
			init = ((ExpressionStatement)iStmnt).getExpression();

			AssignmentExpression assn;
			if(init instanceof AssignmentExpression)
				assignmentExpression((AssignmentExpression)init);
		}
		else System.out.println("ERROR: no expression statement in for loop");

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
			FlatIterator forIter = new FlatIterator(fl.getBody());
			while(forIter.hasNext())
				genCode(forIter.next());

			//generate code to update loop variable
			if(step instanceof CommaExpression)
				commaExpression((CommaExpression)step);
			else if(step instanceof AssignmentExpression)
				assignmentExpression((AssignmentExpression)step);
			else System.out.println("\n\nERROR in step of for loop\n\n");

			//generate unconditional branch to start of loop and comparison
			code.println("br label %loop"+ (loopLabel-3));

			//generate end label
			code.println("loop"+(loopLabel-1) +":");
		} 
		else{code.println("_________ERROR: binray expressions only handled for while loop");}
	}
	private void whileLoop(WhileLoop wl){
		dump.println("While loop found");
		Expression lc = wl.getCondition();
		dump.println("While loop conditions:"+lc);
		boolean LHSIsArray = false;
		boolean LHSIs2dArray = false;
		boolean RHSIsArray = false;
		boolean RHSIs2dArray = false;
		String LHSArrayLocation = null;
		String LHSArrayLocation2 = null;
		String RHSArrayLocation = null;
		String RHSArrayLocation2 = null;
		String nameLHS = null;
		String nameRHS = null;
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
			else if(LHS instanceof ArrayAccess){
				String name=null;
				LHSIsArray = true;
				ArrayAccess aL = (ArrayAccess) LHS;
				nameLHS = aL.getArrayName().toString();
				LHSArrayLocation=aL.getIndices().get(0).toString();
				if(aL.getNumIndices() > 1) {
					LHSIs2dArray = true;
					LHSArrayLocation2=aL.getIndices().get(1).toString();
				}
				if(!LHSIs2dArray){
					 String nameOfArray = nameLHS;
					nameLHS = new String(nameLHS+"_"+LHSArrayLocation);
					code.println("%"+nameLHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+LHSArrayLocation);
					code.println("%"+nameLHS+" = load i32* "+nameLHS);
				}
				else if (LHSIs2dArray){
					String nameOfArray = nameLHS;
					nameLHS = new String(nameOfArray+"_"+LHSArrayLocation+"_"+LHSArrayLocation2);
					code.println("%"+nameLHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+LHSArrayLocation+", i32 "+LHSArrayLocation2);
					code.println("%"+nameLHS+" = load i32* "+nameLHS);
				}
			}
			//gen RHS register if needed
			if(RHS instanceof BinaryExpression)
				RHSreg = genExpressionCode((BinaryExpression) RHS);
			else if(RHS instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				RHSreg = ssaReg-1;
			}
			else if(RHS instanceof ArrayAccess){
				String name=null;
				RHSIsArray = true;
				ArrayAccess aL = (ArrayAccess) RHS;
				nameRHS = aL.getArrayName().toString();
				RHSArrayLocation=aL.getIndices().get(0).toString();
				if(aL.getNumIndices() > 1) {
					RHSIs2dArray = true;
					RHSArrayLocation2=aL.getIndices().get(1).toString();
				}
				if(!RHSIs2dArray){
					 String nameOfArray = nameRHS;
					nameLHS = new String(nameRHS+"_"+RHSArrayLocation);
					code.println("%"+nameRHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+RHSArrayLocation);
					code.println("%"+nameRHS+" = load i32* "+nameRHS);
				}
				else if (RHSIs2dArray){
					String nameOfArray = nameRHS;
					nameRHS = new String(nameOfArray+"_"+RHSArrayLocation+"_"+RHSArrayLocation2);
					code.println("%"+nameRHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+RHSArrayLocation+", i32 "+RHSArrayLocation2);
					code.println("%"+nameRHS+" = load i32* "+nameRHS);
				}
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
			else if(LHSIsArray)
				code.print("%"+nameLHS+", ");
			else
				code.print("%" + LHSreg + ", ");

			if(RHS instanceof IntegerLiteral)
				code.println(((IntegerLiteral) RHS).getValue());
			else if(RHS instanceof ArrayAccess)
				code.print("%"+nameRHS+", ");
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

		//create code
		if (!(proc.getParameters().isEmpty() || proc.getParameter(0).toString().equals("void ")))
		{
			String parameter = proc.getParameter(0).toString();
			if (parameter.startsWith("int"))
				argBuff.append("i32 %" + parameter.substring(parameter.indexOf("t") +2));
			
			for (int i = 1; i < proc.getParameters().size(); i++ ) {
				argBuff.append(", ");
				parameter = proc.getParameter(i).toString();
				if (parameter.startsWith("int"))
					argBuff.append("i32 %" + parameter.substring(parameter.indexOf("t") +2));
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
		if(retType.equals("int")) {
			code.println("%retval"+currentRetVal++ + " = alloca i32");
		}

		while(procIter.hasNext())		//iterate on body of procedure
		{
			genCode(procIter.next());             //get statements and generate code   
		}

		code.println("}\n");

		return false;
	}  


	private boolean foundReturn(ReturnStatement rs){
		Expression ex = rs.getExpression();
		dump.println("Return value: "+ex);

		//print code
		if(ex instanceof BinaryExpression)
		{
			int resultReg = genExpressionCode((BinaryExpression)ex);	
			code.println("store i32 %"+resultReg+", i32* %retval"+(currentRetVal-1));
			code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		else if(ex instanceof Identifier)
		{
			code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)ex).getName());
			
			code.println("store i32 %"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
			code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		else if(ex instanceof IntegerLiteral)
		{
			code.println("%"+ ssaReg++ +" = "+ex.toString());
			code.println("store i32 %"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
			code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		
		
		
		/*
		code.println("%"+ ssaReg++ +" = "+ex.toString());
		code.println("store i32 %"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
		code.println("return_"+currentRetVal+":");
		code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
		code.println("ret i32 %retval"+(currentRetVal-1));
		*/
		return false;
	}

	private void genCode(Object o){
		//debug.println("\n___________Object"+o.getClass());
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
		else if (o instanceof ExpressionStatement){
			Expression exp = ((ExpressionStatement)o).getExpression();
			if(exp instanceof AssignmentExpression)
				assignmentExpression((AssignmentExpression)exp);
			else if(exp instanceof FunctionCall)
				functionCall((FunctionCall) exp);				
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

	private int assignmentExpression(AssignmentExpression assn)
	{
		//Setup variables
		int returnReg = -1;
		boolean LHSIsArray = false;
		boolean LHSIs2dArray = false;
		boolean RHSIsArray = false;
		boolean RHSIs2dArray = false;
		String LHSArrayLocation = null;
		String LHSArrayLocation2 = null;
		String RHSArrayLocation = null;
		String RHSArrayLocation2 = null;
		Expression LHS = assn.getLHS();
		Expression RHS = assn.getRHS();
		String nameLHS = null;
		String nameRHS = null;
		
		if(LHS instanceof ArrayAccess){
			String name=null;
			LHSIsArray = true;
			ArrayAccess aL = (ArrayAccess) LHS;
			nameLHS = aL.getArrayName().toString();
			LHSArrayLocation=aL.getIndices().get(0).toString();
			if(aL.getNumIndices() > 1) {
				LHSIs2dArray = true;
				LHSArrayLocation2=aL.getIndices().get(1).toString();
			}
			if(!LHSIs2dArray){
				 String nameOfArray = nameLHS;
				nameLHS = new String(nameLHS+"_"+LHSArrayLocation);
				code.println("%"+nameLHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+LHSArrayLocation);
			}
			else if (LHSIs2dArray){
				String nameOfArray = nameLHS;
				nameLHS = new String(nameOfArray+"_"+LHSArrayLocation+"_"+LHSArrayLocation2);
				code.println("%"+nameLHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+LHSArrayLocation+", i32 "+LHSArrayLocation2);
			}
			
		}
		else {
			nameLHS = LHS.toString();
		}
		if(RHS instanceof BinaryExpression)
		{
			returnReg = genExpressionCode((BinaryExpression) RHS);
			code.println("store i32 %" + returnReg + ", i32* %" + nameLHS);
		}
		else if(RHS instanceof Identifier)
		{
			code.println("%" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
			code.println("store i32 %"+ (ssaReg-1) + ", i32* %"+nameLHS);
			returnReg = ssaReg - 1;
		}
		else if(RHS instanceof ArrayAccess){
			String nameAA;
			ArrayAccess aR = (ArrayAccess) RHS;
			nameRHS = aR.getArrayName().toString();
			RHSArrayLocation=aR.getIndices().get(0).toString();
			
			if(aR.getNumIndices() > 1) {
				RHSIs2dArray = true;
				RHSArrayLocation2=aR.getIndices().get(1).toString();
			}
	
			if(!RHSIs2dArray){
				nameAA = new String(nameRHS+"_"+RHSArrayLocation);
				code.println("%"+nameAA+" = getelementptr inbounds %"+nameRHS+", i32 "+RHSArrayLocation);
			}
			else {
				nameAA = new String(nameRHS+"_"+RHSArrayLocation+"_"+RHSArrayLocation2);
				code.println("%"+nameAA+" = getelementptr inbounds %"+nameRHS+", i32 "+RHSArrayLocation+", i32 "+RHSArrayLocation2);
			}
				dump.println("nl:"+nameLHS);
				code.println("%"+nameLHS+" = load i32* "+nameAA);
			
		}
		else if(RHS instanceof IntegerLiteral)
		{
			returnReg = ssaReg++;
			code.println("%" + returnReg + " = " + ((IntegerLiteral)RHS).getValue());
			code.println("store i32 "+ ((IntegerLiteral)RHS).getValue() + ", i32* %"+nameLHS);
		}
		else if(RHS instanceof CommaExpression){
			returnReg = commaExpression((CommaExpression)RHS);
			code.println("store i32 %"+ returnReg +", i32* %"+nameLHS);
		}
else if(RHS instanceof FunctionCall)
		{
			returnReg = functionCall((FunctionCall) RHS);
			code.println("store i32 %"+returnReg+", i32* %"+nameLHS);
		}
		else if(RHS instanceof UnaryExpression){
			boolean global = true;
			code.print("store i32");

			//debug.println("LHS = " + LHS);
			//debug.println("RHS = " + RHS);
			
			//debug.println(assn.getParent().getParent().getChildren());

			DepthFirstIterator children = new DepthFirstIterator(assn.getParent().getParent());
			children = new DepthFirstIterator(children.next());	
			
			String assigned = RHS.toString().substring(RHS.toString().indexOf("&")+2,RHS.toString().length() - 1);
			//debug.println(assigned);
			
			while (children.hasNext())
			{
				Object child = children.next();

				if(child instanceof VariableDeclaration)    //global variable declarations
				{
					for(int k = 0; k < ((VariableDeclaration) child).getNumDeclarators(); k++)
					{
						VariableDeclarator referencedDec = (VariableDeclarator) ((VariableDeclaration) child).getDeclarator(k);

						if (referencedDec.getID().toString().equals(assigned))
						{
							global = false;
							
							int derefCount = referencedDec.getTypeSpecifiers().size();
							
							for (int j = 0; j < derefCount; j++) {
								code.print("*");
							}
							
							code.print(" %"+ referencedDec.getID() + ", i32");
							
							for (int j = 0; j <= derefCount; j++) {
								code.print("*");
							}
							
							code.println(" %"+ LHS);
						}
					}
				}
			}
			if (global == true)
			{
				FlatIterator globalChildren = new FlatIterator(program);
				globalChildren = new FlatIterator(globalChildren.next());	
				
				assigned = RHS.toString().substring(RHS.toString().indexOf("&")+2,RHS.toString().length() - 1);
								
				while (globalChildren.hasNext())
				{
					Object child = globalChildren.next();

					if(child instanceof VariableDeclaration)    //global variable declarations
					{						
						for(int k = 0; k < ((VariableDeclaration) child).getNumDeclarators(); k++)
						{
							VariableDeclarator referencedDec = (VariableDeclarator) ((VariableDeclaration) child).getDeclarator(k);

							if (referencedDec.getID().toString().equals(assigned))
							{								
								int derefCount = referencedDec.getTypeSpecifiers().size();
								
								for (int j = 0; j < derefCount; j++) {
									code.print("*");
								}
								
								code.print(" %"+ referencedDec.getID() + ", i32");
								
								for (int j = 0; j <= derefCount; j++) {
									code.print("*");
								}
								
								code.println(" %"+ LHS);
							}
						}
					}
				}
			}
		}

		return returnReg;
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
			instrBuff = instrBuff.append("%" + (ssaReg-1));
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
	private int commaExpression(CommaExpression ce)
	{
		FlatIterator commaIter = new FlatIterator(ce);
		
		int returnReg = -1;
		
		while(commaIter.hasNext())
		{
			Object o = commaIter.next();
			
			if(o instanceof AssignmentExpression)
			{
				assignmentExpression((AssignmentExpression) o);
			}
			else if(o instanceof BinaryExpression)
			{
				returnReg = genExpressionCode((BinaryExpression) o);
			}
			else if(o instanceof Identifier)
			{
				code.println("%" + ssaReg++ + " = load i32* %"+((Identifier) o).getName());
				returnReg = ssaReg - 1;
			}
			else if(o instanceof IntegerLiteral)
			{
				returnReg = ssaReg++;
				code.println("%" + returnReg + " = " + ((IntegerLiteral) o).getValue());
			}
			else if(o instanceof CommaExpression)
			{
				returnReg = commaExpression((CommaExpression) o);
			}
		}
		return returnReg;
	}	
	private int functionCall(FunctionCall fc)
	{
		String returnType = fc.getReturnType().toString();
		int beginReg=0, endReg=0;
		int returnReg = -1;
		
		//get function arguments and put in registers
		if(fc.getNumArguments() != 0)
			beginReg = ssaReg;
		for(int i=0;i<fc.getNumArguments();i++)
		{
			endReg = ssaReg;
			code.println("%"+ ssaReg++ + " = load i32* %"+fc.getArgument(i));
		}
		
		//print call code
		if(returnType.equals("[int]"))
		{
			returnReg = ssaReg;
			code.print("%"+ ssaReg++ + " = ");
		}
		code.print("call "+returnType.substring(returnType.indexOf('[')+1, returnType.indexOf(']'))+
						" @"+fc.getName()+"(");
		
		//add args
		for(int i=beginReg; i<=endReg;i++)
		{
			if(i>0)
				code.print(", ");
			code.print("i32 %"+i);
		}
		code.println(")");
		return returnReg;
	}
}
