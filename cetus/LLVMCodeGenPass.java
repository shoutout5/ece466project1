import java.io.*;
import java.lang.reflect.Method;
import java.util.*;
import java.util.List;
import java.util.ArrayList;

import cetus.hir.*;
import cetus.exec.*;
import cetus.analysis.*;

public class LLVMCodeGenPass extends cetus.analysis.AnalysisPass
{
	int errors;
	int currentRetVal = 0;
	int ssaReg = 1;
	int ifLabel = 0;
	int loopLabel = 0;
	int strConst = 0;
	HashMap ListOfArrays=new HashMap();					// list of arrays
	HashMap ListOfPointers = new HashMap();				// list of pointers
	HashMap ListOfStrings = new HashMap();				// list of string literals 
	HashMap parameters = new HashMap();					// list of function parameters
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
		
		// iterate through all code to find String Literals for printf() and scanf()
		FlatIterator g = new FlatIterator(program);
		DepthFirstIterator findStrings = new DepthFirstIterator(g.next());
		while(findStrings.hasNext())
		{
			Object o = findStrings.next();
			// if string literal add to string constants for code
			if(o instanceof StringLiteral)
			{
				StringLiteral sl = (StringLiteral)o;
				String fmtString = sl.getValue();
				//if string does not already exist add to hash map
				if(ListOfStrings.get(fmtString) == null)
				{
					ListOfStrings.put(fmtString, strConst);
				
					int numChars = fmtString.length();
					fmtString = fmtString.concat("\\00");
					
					//print string constant to code
					code.println("@.str" + strConst++ + " = private unnamed_addr constant [" +
							(numChars+1) + " x i8] c\"" + fmtString + "\"");
				}
			}
		}
		
		//begin codeing rest of program
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

		iter.reset();	// go back to the top of the table

		code.println("");

		while(iter.hasNext())	// before we've reached the end of the program
		{
			Object o = iter.next();             //get object
			//code.println("\n___________Object"+o.getClass());
			if(o instanceof Procedure){
				procedure((Procedure) o);
			}
		}

		if(verbosity>0)
		{	
			System.out.println("Dump Ouput:");
			dump.flush();
			System.out.println("\n\nDebug Output:\n");
			debug.flush();
		}

		//add definitions for printf() and scanf()
		code.println("\n\n");
		code.println("declare i32 @scanf(i8*, ...)");
		code.println("declare i32 @printf(i8*, ...)");

		//print all dump and code to screen at end
		
		code.flush();
		
	} 

	private void declareVariable(VariableDeclaration varDec)	// handling of local variables
	{
		String initVal = new String("0");	// placeholder for variable initializer
		
		//work on all declarations in statement if more than one declared on a line
		for(int i = 0; i < varDec.getNumDeclarators(); i++)
		{
			VariableDeclarator dec = (VariableDeclarator) varDec.getDeclarator(i);
			IDExpression id = dec.getID();									// get name of declarator
			dump.println("Var ID: " + id.getName());
			String arraySize = dec.getArraySpecifiers().toString().trim();	// get length of array
			boolean isArray;
			boolean is2dArray;
			String arraySpec=null;											//Array sizes

			//try to get the arraySize and pull out just the number. 
			try{									
				arraySize = arraySize.substring(2,arraySize.lastIndexOf("]")-1 ).trim();
				isArray=true;
				if(arraySize.contains("]["))	// array is 2d if has two sets of brackets
					is2dArray = true;
				else
					is2dArray = false;
				
				//if the array is 2d then break each dimension down into parts. 
				if(is2dArray){ 
					String sizeOne = arraySize.substring(0,arraySize.indexOf("]["));
					String sizeTwo = arraySize.substring(arraySize.indexOf("][")+2);
					arraySpec= new String("[ "+sizeOne+" ["+sizeTwo+" x i32]]");
				} else {
					arraySpec= new String("["+arraySize+" x i32]");
				}
			}
			//if the try fails then the object isn't an array
			catch(StringIndexOutOfBoundsException e){
				isArray=false;
			}
			//check for possible initializer
			try {
				Initializer init = dec.getInitializer();
				dump.println("Value Init");
				
				//if it is an array add it to the list for future reference and allocate it
				if(isArray){
					ListOfArrays.put(id.getName(), arraySpec);
					code.println("%" + id.getName() + " = alloca "+arraySpec);
				}
				else	// just a variable
				{
					//allocate the space for non-arrays
					code.print("%" + id.getName() + " = alloca");
					//if it is an integer type assign it
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
				if (dec.getTypeSpecifiers().size() == 1)	// just a type specifier, not a pointer
				{
					if(init != null)	// has an initial value
					{
						initVal = init.toString();
						initVal = initVal.substring(initVal.indexOf("=")+2,initVal.length());
					} 
					if(!isArray)		// not an array
						code.println("store i32 " + initVal + ", i32* %" + id.getName());
				}
				else // pointers
				{
					ListOfPointers.put(id.getName(), dec.getTypeSpecifiers().size());
					if (init != null)	// has an initial value
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
						code.println("");	// otherwise new line
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
			if(id.getName().toString().equals("printf") || id.getName().toString().equals("scanf"))
				return;
			dump.println("Var ID: " + id.getName());
			//dump.println("Specifiers = " + dec.getSpecifiers());
			//dump.println("Type Specifiers = " + dec.getTypeSpecifiers());
			//dump.println("Parent: " + varDec.getParent() + "\n");
			String arraySize;

			try{
				arraySize = dec.getArraySpecifiers().toString().trim();	// get array parameters
				arraySize = arraySize.substring(2,arraySize.lastIndexOf("]")-1 ).trim();	// get array dimensions from [ ]
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

						while (children.hasNext())	// while there are more statements
						{
							Object child = children.next();	// go to the next statement

							if(child instanceof VariableDeclaration)    //global variable declarations
							{
								if((((VariableDeclaration) child).getParent()) instanceof TranslationUnit)	// if vardec is global
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
		int    LHSArgReg = -1;
		String LHSArrayLocation = null;
		String LHSArrayLocation2 = null;
		String RHSArrayLocation = null;
		String RHSArrayLocation2 = null;
		String nameLHS = null;
		String nameRHS = null;
		StringBuffer setupInstr = new StringBuffer("");
		
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
				if(parameters.get(((Identifier)LHS).getName()) != null)
				{
					LHSArgReg = Integer.parseInt(parameters.get(((Identifier)LHS).getName()).toString());
					code.println("%r"+ ssaReg++ + " = load i32* %r"+LHSArgReg);
					LHSArgReg = ssaReg - 1;
				}
				else
				{				
					code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)LHS).getName());
					LHSreg = ssaReg-1;
				}
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
					try{
						int x = Integer.parseInt(LHSArrayLocation);
						code.println("%r"+ssaReg++ +" = getelementptr inbounds "+ListOfArrays.get(nameOfArray)+"* %"+nameOfArray+", i32 0, i32 "+LHSArrayLocation);
					}
					catch(NumberFormatException e){
						code.println("%r"+ssaReg++ +" = getelementptr inbounds "+ListOfArrays.get(nameOfArray)+"* %"+nameOfArray+", i32 0, i32* "+LHSArrayLocation);
					}
					code.println("%r"+ssaReg++ +" = load i32* %r"+(ssaReg-2));
					nameLHS = new String("r"+(ssaReg-1));
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
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				RHSreg = ssaReg-1;
			}
			else if(RHS instanceof ArrayAccess){
				dump.println("here");
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
					
					code.println("%r"+ssaReg++ +" = getelementptr inbounds %"+nameOfArray+", i32 0, i32 "+RHSArrayLocation);
					code.println("%r"+ssaReg++ +" = load i32* %r"+(ssaReg-2));
				}
				else if (RHSIs2dArray){
					String nameOfArray = nameRHS;
					nameRHS = new String(nameOfArray+"_"+RHSArrayLocation+"_"+RHSArrayLocation2);
					code.println("%"+nameRHS+" = getelementptr inbounds %"+nameOfArray+", i32 "+RHSArrayLocation+", i32 "+RHSArrayLocation2);
					code.println("%"+nameRHS+" = load i32* "+nameRHS);
				}
			}

			
			if(terms instanceof IntegerLiteral){
				code.println("%r"+ssaReg++ +" = icmp ne i32 0, "+((IntegerLiteral) terms).getValue());
			}
			else if(exp instanceof AssignmentExpression) {
				int regNum = assignmentExpression((AssignmentExpression) exp);
				code.println("%r"+ssaReg++ +" = icmp ne i32 0, %r"+regNum);
			}
			else if(terms instanceof UnaryExpression){
				code.println("%r"+ssaReg++ +" = load i32* "+((UnaryExpression) terms).getExpression());
				code.println("%r"+ssaReg++ +" = icmp ne i32 0, %r"+ssaReg--);
				ssaReg++;
			}
			else {
				
				setupInstr.append("%r" + ssaReg++ + " = icmp ");  //first part of compare expression
				
				//generate type of comparison
				if(exp.getOperator().toString().trim().equals("<")) setupInstr.append("slt ");
				else if(exp.getOperator().toString().trim().equals(">")) setupInstr.append("sgt ");
				else if(exp.getOperator().toString().trim().equals(">=")) setupInstr.append("sge ");
				else if(exp.getOperator().toString().trim().equals("<=")) setupInstr.append("sle ");
				else if(exp.getOperator().toString().trim().equals("==")) setupInstr.append("eq ");
				else if(exp.getOperator().toString().trim().equals("!=")) setupInstr.append("ne ");
			
				setupInstr.append("i32 ");
				code.print(setupInstr.toString());
			if(LHS instanceof IntegerLiteral)
					code.print(((IntegerLiteral) LHS).getValue() + ", ");
				else if(LHSIsArray)
					code.print("%"+nameLHS+", ");
				else if(LHSArgReg != -1)
					code.print("%r"+LHSArgReg+", ");
				else
					code.print("%r" + LHSreg + ", ");

				if(RHS instanceof IntegerLiteral)
					code.println(((IntegerLiteral) RHS).getValue());
				else if(RHSIsArray)
					code.print("%"+nameRHS+", ");
				else
					code.println("%r" + RHSreg);
			}
			code.println("br i1 %r"+(ssaReg-1)+", label %ifLabel"+ ifLabel++ +", label %ifLabel"+ ifLabel++);
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
			code.println("br label %loop" + loopLabel);
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
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)LHS).getName());
				LHSreg = ssaReg-1;
			}
			//gen RHS register if needed
			if(RHS instanceof BinaryExpression)
				RHSreg = genExpressionCode((BinaryExpression) RHS);
			else if(RHS instanceof Identifier)
			{
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				RHSreg = ssaReg-1;
			}

			//generate comparison statement
			code.print("%r" + ssaReg++ + " = icmp ");		//first part of compare expression
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
				code.print("%r" + LHSreg + ", ");

			if(RHS instanceof IntegerLiteral)
				code.println(((IntegerLiteral) RHS).getValue());
			else
				code.println("%r" + RHSreg);

			//generate branch statement
			code.println("br i1 %r"+(ssaReg-1)+", label %loop"+ loopLabel++ +", label %loop"+ loopLabel++);
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
		StringBuffer setupInstr = new StringBuffer("");
		if(lc instanceof BinaryExpression)
		{
			BinaryExpression exp = (BinaryExpression) lc;

			//generate top of loop label
			code.println("br label %loop" + loopLabel);
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
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)LHS).getName());
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
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
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
			setupInstr.append("%r" + ssaReg++ + " = icmp ");		//first part of compare expression
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
				code.print("%r" + LHSreg + ", ");

			if(RHS instanceof IntegerLiteral)
				code.println(((IntegerLiteral) RHS).getValue());
			else if(RHS instanceof ArrayAccess)
				code.print("%"+nameRHS+", ");
			else
				code.println("%r" + RHSreg);

			//generate branch statement
			code.println("br i1 %r"+(ssaReg-1)+", label %loop"+ loopLabel++ +", label %loop"+ loopLabel++);
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

	private boolean procedure(Procedure proc)
	{
		StringBuffer argBuff = new StringBuffer("");
		FlatIterator procIter = new FlatIterator(proc.getBody());		//set up iterator on body of procedure
		IDExpression id = proc.getName();
		List ll = proc.getReturnType();
		int startReg=0, endReg=0;
		dump.println("Return type is "+ll.get(0));
		//List l2 = proc.getParameters();
		//dump.println("Parameters"+l2.get(0));
		dump.println("The name of this function is "+id.getName());
		CompoundStatement cs = proc.getBody();
		//dump.println("There are "+cs.countStatements()+" statements in this function.");
		parameters.clear();				//clear parameters for new function

		//create code
		if (!(proc.getParameters().isEmpty() || proc.getParameter(0).toString().equals("void ")))
		{
			String parameter = proc.getParameter(0).toString();
			if (parameter.startsWith("int"))
			{
				argBuff.append("i32 %" + parameter.substring(parameter.indexOf("t") +2));
				startReg=ssaReg++;
				debug.println("begin"+startReg);
				endReg=startReg;
				parameters.put(parameter.substring(parameter.indexOf("t") +2), startReg);
			}
			
			for (int i = 1; i < proc.getParameters().size(); i++ ) {
				argBuff.append(", ");
				parameter = proc.getParameter(i).toString();
				if (parameter.startsWith("int"))
				{
					argBuff.append("i32 %" + parameter.substring(parameter.indexOf("t") +2));
					endReg=ssaReg++;
					debug.println("seconde"+endReg);
					parameters.put(parameter.substring(parameter.indexOf("t") +2), endReg);
				}
			}
			//System.out.println("Arguments: " + argBuff);
		}

		String retType = ll.get(0).toString();
		code.print("define ");
		if(retType.equals("int"))
			code.print("i32 ");
		else						// no return type
			code.print("void ");

		code.print("@"+id.getName()+"("+argBuff+") ");
		code.println("nounwind ssp{");
		code.println("entry_"+id.getName()+":");
		if(retType.equals("int")) {
			code.println("%retval"+currentRetVal++ + " = alloca i32");
		}
		
		// allocate stack for parameters
		if(!(proc.getParameters().isEmpty() || proc.getParameter(0).toString().equals("void ")))
			for(int i=startReg;i<=endReg;i++)
			{
				String param = proc.getParameter(i-startReg).toString();
				param = param.substring(param.indexOf("t") +2);
				code.println("%r"+i+" = alloca i32");
				code.println("store i32 %" + param + ", i32* %r"+ i);
			}

		while(procIter.hasNext())		// iterate on body of procedure
		{
			genCode(procIter.next());	//get statements and generate code   
		}

		code.println("}\n");
		
		parameters.clear();				//done with parameters clear for next function

		return false;
	}  


	private boolean foundReturn(ReturnStatement rs){
		Expression ex = rs.getExpression();
		dump.println("Return value: "+ex);

		//print code
		if(ex instanceof BinaryExpression)
		{
			int resultReg = genExpressionCode((BinaryExpression)ex);	
			code.println("store i32 %r"+resultReg+", i32* %retval"+(currentRetVal-1));
			//code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		else if(ex instanceof Identifier)
		{
			code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)ex).getName());
		
			code.println("store i32 %r"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
			//code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		else if(ex instanceof IntegerLiteral)
		{
			code.println("%r" + ssaReg++ +" = add i32 0, "+ex.toString());
			code.println("store i32 %r"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
			//code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		else if(ex instanceof FunctionCall)
		{
			debug.println("FunctionCall");
			int resultReg = functionCall((FunctionCall)ex);
			code.println("store i32 %r"+resultReg+", i32* %retval"+(currentRetVal-1));
			//code.println("return_"+currentRetVal+":");
			code.println("%retval"+ currentRetVal++ +" = load i32* %retval"+(currentRetVal-2));
			code.println("ret i32 %retval"+(currentRetVal-1));
		}
		
		
		
		/*
		code.println("%r" + ssaReg++ +" = "+ex.toString());
		code.println("store i32 %"+(ssaReg-1)+", i32* %retval"+(currentRetVal-1));
		//code.println("return_"+currentRetVal+":");
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
		
		if(LHS instanceof ArrayAccess){		// if left hand side is not a 2d array
			String name=null;
			LHSIsArray = true;
			ArrayAccess aL = (ArrayAccess) LHS;
			nameLHS = aL.getArrayName().toString();
			LHSArrayLocation=aL.getIndices().get(0).toString();
			String LHSArrayLocation1;
			try{
				int LHSint = Integer.parseInt(LHSArrayLocation);
				dump.println("try block for array ");
				LHSArrayLocation1 = LHSArrayLocation;
			}
			catch(Exception e){
				code.println("%r" + ssaReg++ + " = load i32* %"+LHSArrayLocation);
				LHSArrayLocation1 = new String("%r"+(ssaReg-1));
			}
			if(aL.getNumIndices() > 1) {
				LHSIs2dArray = true;
				LHSArrayLocation2=aL.getIndices().get(1).toString();
			}
			if(!LHSIs2dArray){				// if left hand side is not a 2d array
				 String nameOfArray = nameLHS;
				nameLHS = new String(nameLHS+"_"+LHSArrayLocation);
				if(LHSArrayLocation.equals(LHSArrayLocation1))
					code.println("%r"+ssaReg++ +" = getelementptr inbounds "+ListOfArrays.get(nameOfArray)+"* %"+nameOfArray+", i32 "+LHSArrayLocation1);
				else
					code.println("%r"+ssaReg++ +" = getelementptr inbounds "+ListOfArrays.get(nameOfArray)+"* %"+nameOfArray+", i32 "+LHSArrayLocation1);
			}
			else if (LHSIs2dArray){			// otherwise if left hand side is 2d array
				String nameOfArray = nameLHS;
				nameLHS = new String(nameOfArray+"_"+LHSArrayLocation+"_"+LHSArrayLocation2);
				code.println("%r"+ssaReg++ +" = getelementptr inbounds "+ListOfArrays.get(nameOfArray)+"** %"+nameOfArray+", i32 "+LHSArrayLocation+", i32 "+LHSArrayLocation2);
			}
			
		}
		else {
			nameLHS = LHS.toString();
		}
		nameRHS = RHS.toString();
		
		if(RHS instanceof BinaryExpression)
		{
			returnReg = genExpressionCode((BinaryExpression) RHS);
			
			String LHSsubstring;
			int derefCount = 0;
			
			try{
				LHSsubstring = LHS.toString().substring(2,LHS.toString().length());
			}
			catch (Exception e)
			{
				LHSsubstring = "";
			}
			
			//System.out.println(LHSsubstring);
			
			if (LHSsubstring.startsWith("*") || LHSsubstring.startsWith("("))
			{
				while (LHSsubstring.startsWith("*") || LHSsubstring.startsWith("("))
				{
					try{
						//debug.println(LHSsubstring);
						LHSsubstring = LHSsubstring.substring(LHSsubstring.indexOf("*") + 2,LHSsubstring.length());
						derefCount++;
					}
					catch (Exception e)
					{
						break;
					}
				}
				//debug.println(derefCount);
				for (int i = derefCount; i > 0; i--)
				{
					code.print("%r" + ssaReg++ + " = load i32");

					for (int j = 0; j <= i; j++)
						code.print("*");

					code.print(" %");

					if (i == derefCount)
						code.println(nameLHS.substring(nameLHS.lastIndexOf("*") + 2,nameLHS.lastIndexOf("*") + 3));
					else
						code.println("r"+(ssaReg - 2));
				}
				
				code.println("store i32 %r" + returnReg + ", i32* %r" + (ssaReg - 1));
			}
			else
			{
				//code.println("right here");
				code.print("store i32");
				if (ListOfPointers.containsKey(nameLHS.toString()))
					for (int i = 1; i < Integer.parseInt(ListOfPointers.get(nameLHS).toString()); i++) { 	// count number of references
						code.print("*");
					}	
				code.print(" %r" + returnReg + ", i32*");
				if (ListOfPointers.containsKey(nameLHS.toString()))
					for (int i = 1; i < Integer.parseInt(ListOfPointers.get(nameLHS).toString()); i++) { 	// count number of references
						code.print("*");
					}
				//if (ListOfPointers.containsKey(nameLHS.toString()))
						code.println(" %" + nameLHS.toString());
					//	else
						//	code.println(" %r" + (returnReg+1));
			}			
		}
		else if(RHS instanceof Identifier)
		{
			if(ListOfArrays.containsKey(nameRHS)){	// if variable name is in the array table (is an array)
				dump.println("name:"+nameRHS+"key dump: "+ListOfArrays.get(nameRHS));
				code.println("%r" + ssaReg++ + " = getelementptr "+ListOfArrays.get(nameRHS)+"* %"+nameRHS+", i32 0, i32 0");
				if (ListOfPointers.containsKey(nameLHS))
				{
					code.print("store i32");

					for (int i = 1; i < Integer.parseInt(ListOfPointers.get(nameLHS).toString()); i++) {	// count number of references (-1)
						code.print("*");
					}

					code.print(" %r" + (ssaReg - 1) + ", i32");
					
					for (int i = 0; i < Integer.parseInt(ListOfPointers.get(nameLHS).toString()); i++) { 	// count number of references
						code.print("*");
					}
					
					code.println(" %" + nameLHS);
				}
			} 
			else {
				
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier)RHS).getName());
				
				code.println("store i32 %r"+ (ssaReg-1) + ", i32* %"+((Identifier)RHS).getName());
			}
			returnReg = ssaReg - 1;
		}
		else if(RHS instanceof ArrayAccess){	// if right hand side is not a 2d array
			String nameAA;
			ArrayAccess aR = (ArrayAccess) RHS;
			nameRHS = aR.getArrayName().toString();
			RHSArrayLocation=aR.getIndices().get(0).toString();
			
			if(aR.getNumIndices() > 1) {
				RHSIs2dArray = true;
				RHSArrayLocation2=aR.getIndices().get(1).toString();
			}
	
			if(!RHSIs2dArray){	// if left hand side is not a 2d array
				nameAA = new String(nameRHS+"_"+RHSArrayLocation);
				code.println("%"+nameAA+" = getelementptr inbounds "+ListOfArrays.get(nameRHS)+"* %"+nameRHS+", i32 0, i32 "+RHSArrayLocation);
			}
			else {	// if left hand side is a 2d array
				nameAA = new String(nameRHS+"_"+RHSArrayLocation+"_"+RHSArrayLocation2);
				code.println("%"+nameAA+" = getelementptr inbounds "+ListOfArrays.get(nameRHS)+"* %"+nameRHS+", i32 "+RHSArrayLocation+", i32 "+RHSArrayLocation2);
			}
				dump.println("nl:"+nameLHS);
				code.println("%"+nameLHS+" = load i32* "+nameAA);
			
		}
		else if(RHS instanceof IntegerLiteral)
		{
			//debug.println(LHS);
			String LHSsubstring;
			int derefCount = 0;
			
			try{
				LHSsubstring = LHS.toString().substring(2,LHS.toString().length());
			}
			catch (Exception e)
			{
				LHSsubstring = "";
			}
			
			//System.out.println(LHSsubstring);
			
			if (LHSsubstring.startsWith("*") || LHSsubstring.startsWith("("))
			{
				while (LHSsubstring.startsWith("*") || LHSsubstring.startsWith("("))
				{
					try{
						//debug.println(LHSsubstring);
						LHSsubstring = LHSsubstring.substring(LHSsubstring.indexOf("*") + 2,LHSsubstring.length());
						derefCount++;
					}
					catch (Exception e)
					{
						break;
					}
				}
				//debug.println(derefCount);
				for (int i = derefCount; i > 0; i--)
				{
					code.print("%r" + ssaReg++ + " = load i32");

					for (int j = 0; j <= i; j++)
						code.print("*");

					code.print(" %");

					if (i == derefCount)
						code.println(nameLHS.substring(nameLHS.lastIndexOf("*") + 2,nameLHS.lastIndexOf("*") + 3));
					else
						code.println("r"+(ssaReg - 2));
				}
				
				code.println("store i32 "+ ((IntegerLiteral)RHS).getValue() + ", i32* %r" + (ssaReg - 1));
			}
			else
			{
				code.println("store i32 "+ ((IntegerLiteral)RHS).getValue() + ", i32* %"+nameLHS);
			}
			returnReg = ssaReg++;
			code.println("%r" + returnReg + " = add i32 0, " + ((IntegerLiteral)RHS).getValue());
			//code.println("store i32 "+ ((IntegerLiteral)RHS).getValue() + ", i32* %"+nameLHS);
		}
		else if(RHS instanceof CommaExpression){
			String returnString = commaExpression((CommaExpression)RHS);
			try{
				returnReg = Integer.parseInt(returnString);
				code.println("store i32 %r"+ returnReg +", i32* %"+nameLHS);
			}
			catch (Exception e)	
			{
				if (ListOfPointers.containsKey(nameLHS))
				{
					code.print("store i32");

					for (int i = 1; i < Integer.parseInt(ListOfPointers.get(nameLHS).toString()); i++) {	// count number of references (-1)
						code.print("*");
					}

					code.print(" %" + returnString + ", i32");
					
					for (int i = 0; i < Integer.parseInt(ListOfPointers.get(nameLHS).toString()); i++) { 	// count number of references
						code.print("*");
					}
					
					code.println(" %" + nameLHS);
				}
			}
		}
		else if(RHS instanceof FunctionCall)
		{
			returnReg = functionCall((FunctionCall) RHS);
			code.println("store i32 %r"+returnReg+", i32* %"+nameLHS);
		}
		else if(RHS instanceof UnaryExpression){
			boolean global = true;

			//debug.println("LHS = " + LHS);
			//debug.println("RHS = " + RHS);
			
			//debug.println(assn.getParent().getParent().getChildren());

			DepthFirstIterator children = new DepthFirstIterator(assn.getParent().getParent());
			children = new DepthFirstIterator(children.next());	
			
			String assigned = RHS.toString().substring(RHS.toString().indexOf("&")+2,RHS.toString().length() - 1);
			//debug.println(assigned);
			//code.println(assigned);
			
			int index = -1;
			String arrayIndex = null;
			
			try{
				index = assigned.indexOf("[");
				arrayIndex = assigned.substring(index + 1, assigned.indexOf("]"));
				assigned = assigned.substring(0,index);
				code.print("%r" + ssaReg++ + " = getelementptr inbounds");
				//code.print()
			}
			catch (Exception e)
			{
				code.print("store i32");
			}
			
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
							
							if (index != -1)
							{
								code.print(" " + ListOfArrays.get(assigned));
								
							}
							
							for (int j = 0; j < derefCount; j++) {
								code.print("*");
							}
							
							code.print(" %"+ referencedDec.getID() + ", i32");
							
							if (index == -1)
							{
								for (int j = 0; j <= derefCount; j++) {
									code.print("*");
								}
							}
							else
								code.print(" 0");
							
							if (index == -1)
							{
								code.println(" %"+ LHS);
							}
							else
								code.println(", i32 " + arrayIndex);
							
							if (index != -1)
							{
								code.print("store i32");
								for (int j = 0; j < derefCount; j++) {
									code.print("*");
								}
								code.print(" %r" + (ssaReg - 1) + ", i32");
								for (int j = 0; j <= derefCount; j++) {
									code.print("*");
								}
								code.println(" %" + nameLHS);
							}
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
							try{
								VariableDeclarator referencedDec = (VariableDeclarator) ((VariableDeclaration) child).getDeclarator(k);

								if (referencedDec.getID().toString().equals(assigned))
								{								
									int derefCount = referencedDec.getTypeSpecifiers().size();

									for (int j = 0; j < derefCount; j++) {
										code.print("*");
									}

									code.print(" %r"+ referencedDec.getID() + ", i32");

									for (int j = 0; j <= derefCount; j++) {
										code.print("*");
									}

									code.println(" %"+ LHS);
			
								}
							}
							catch(ClassCastException e){}
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
		
		if (! (ListOfPointers.containsKey(LHS.toString())))
		{
			instrBuff = instrBuff.append("%r" + resultReg + " = ");	//print start of instruction
			//decide on function to be used
			if(exp.getOperator().toString().trim().equals("+")) 
				instrBuff = instrBuff.append("add i32 ");
			else if(exp.getOperator().toString().trim().equals("-"))
				instrBuff = instrBuff.append("sub i32 ");
			else if(exp.getOperator().toString().trim().equals("*"))
				instrBuff = instrBuff.append("mul i32 ");
			else if(exp.getOperator().toString().trim().equals("/"))
				instrBuff = instrBuff.append("sdiv i32 ");
		}
		else
		{
			instrBuff = instrBuff.append("%r" + resultReg + " = getelementptr inbounds i32* ");
		}

		//generate code and result registers for left hand size
		if(LHS instanceof IntegerLiteral)
			instrBuff = instrBuff.append(((IntegerLiteral)LHS).getValue());
		else if(LHS instanceof BinaryExpression)
			instrBuff = instrBuff.append("%r" + genExpressionCode((BinaryExpression)LHS));
		else if(LHS instanceof Identifier)
		{
			//load from memory into a register
			setupInstr = setupInstr.append("%r" + ssaReg++ + " = load i32");
			
			if(!parameters.containsKey(((Identifier)LHS).getName()))	//pointer variable
			{
				if (ListOfPointers.containsKey(LHS.toString()))
				{
					for (int i = 1; i < Integer.parseInt(ListOfPointers.get(LHS.toString()).toString()); i++) { 	// count number of references
						setupInstr.append("*");
					}	
				}
				
				setupInstr = setupInstr.append("* %" +
						((Identifier)LHS).getName() + "\n");
			}
			else		//argument variable
			{
				setupInstr.append("* %r"+Integer.parseInt(parameters.get(((Identifier)LHS).getName()).toString())+"\n");
			}
			instrBuff = instrBuff.append("%r" + (ssaReg-1));
		}
		else if(LHS instanceof FunctionCall)
		{
			instrBuff = instrBuff.append("%r" + functionCall((FunctionCall)LHS));
		}
		else if(LHS instanceof ArrayAccess)
			dump.println("fell here0");
		else{
			dump.println("fell here");
			instrBuff = instrBuff.append("%r" + (ssaReg-2));
		}
		
		//generate code and result registers for right hand size
		if(RHS instanceof IntegerLiteral)
		{
			if (! (ListOfPointers.containsKey(LHS.toString())))
				instrBuff = instrBuff.append(", " + ((IntegerLiteral)RHS).getValue());
			else
				instrBuff = instrBuff.append(", i32 " + ((IntegerLiteral)RHS).getValue());
		}
		else if(RHS instanceof BinaryExpression)
			instrBuff = instrBuff.append(", %r" + genExpressionCode((BinaryExpression)RHS));
		else if(RHS instanceof Identifier)
		{
			//load from memory into a register
			if(!parameters.containsKey(((Identifier)RHS).getName()))	//pointer variable
			{
				setupInstr = setupInstr.append("%r" + ssaReg++ + " = load i32* %" +
						((Identifier)RHS).getName() + "\n");
			}
			else		//argument variable
			{
				setupInstr = setupInstr.append("%r" + ssaReg++ + " = load i32* %r" +
						Integer.parseInt(parameters.get(((Identifier)RHS).getName()).toString()) + "\n");
			}
			instrBuff = instrBuff.append(", %r" + (ssaReg-1));
		}

		if(!setupInstr.toString().equals(""))		//print load instructions if required
			code.print(setupInstr);

		code.println(instrBuff);

		return resultReg;
	}
	private String commaExpression(CommaExpression ce)
	{
		FlatIterator commaIter = new FlatIterator(ce);
		
		String returnReg = "-1";
		
		while(commaIter.hasNext())
		{
			Object o = commaIter.next();
			
			if(o instanceof AssignmentExpression)	// if assignment
			{
				assignmentExpression((AssignmentExpression) o);
			}
			else if(o instanceof BinaryExpression)	// if math equation
			{
				returnReg = Integer.toString(genExpressionCode((BinaryExpression) o));
			}
			else if(o instanceof Identifier)
			{
				code.println("%r" + ssaReg++ + " = load i32* %"+((Identifier) o).getName());
				returnReg = Integer.toString(ssaReg - 1);
			}
			else if(o instanceof IntegerLiteral)
			{
				returnReg = Integer.toString(ssaReg++);
				code.println("%r" + returnReg + " = add i32 0, " + ((IntegerLiteral) o).getValue());
			}
			else if(o instanceof CommaExpression)
			{
				returnReg = commaExpression((CommaExpression) o);
			}
			else if(o instanceof UnaryExpression)
			{
				//System.out.println("o = " + o.toString());	
				returnReg = o.toString().substring(o.toString().indexOf("&") + 2, o.toString().indexOf("&") + 3);
			}
		}
		return returnReg;
	}	
	private int functionCall(FunctionCall fc)
	{
		String returnType = fc.getReturnType().toString();
		int beginReg=0, endReg=0;
		int returnReg = -1;
		
		//check for printf() or scanf() function to be handled
		if(fc.getName().toString().equals("scanf"))
		{
			return scanfCall(fc);
		}
		else if(fc.getName().toString().equals("printf"))
		{
			return printfCall(fc);
		}
		
		//get function arguments and put in registers
		if(fc.getNumArguments() != 0)
		{
			beginReg = ssaReg;
			endReg = beginReg + fc.getNumArguments() - 1;
			ssaReg += fc.getNumArguments();
		}
		for(int i=0;i<fc.getNumArguments();i++)
		{
			int resultReg;
			//endReg = ssaReg;
			if(fc.getArgument(i) instanceof BinaryExpression)
			{
				resultReg = genExpressionCode((BinaryExpression)(fc.getArgument(i)));
				code.println("%r" + (beginReg+i) + " = add i32 0, %r" + resultReg);
			}
			else
				code.println("%r" + (beginReg+i) + " = load i32* %"+fc.getArgument(i));
		}
		
		//print call code
		if(returnType.equals("[int]"))
		{
			returnReg = ssaReg;
			code.print("%r" + ssaReg++ + " = ");
		}
		code.print("call "+returnType.substring(returnType.indexOf('[')+1, returnType.indexOf(']'))+
						" @"+fc.getName()+"(");
		
		//add args
		for(int i=beginReg; i<=endReg;i++)
		{
			if(i-beginReg>0)
				code.print(", ");
			code.print("i32 %r"+i);
		}
		code.println(")");
		return returnReg;
	}
	
	private int scanfCall(FunctionCall fc)
	{
		debug.println("scanf() function found");
		debug.println(fc.getArgument(0));
		int strNum;
		//get format String Argument and trim
		String fmtString = fc.getArgument(0).toString();
		fmtString = fmtString.substring(fmtString.indexOf('"')+1, fmtString.length());
		fmtString = fmtString.substring(0, fmtString.indexOf('"'));
		int numChars = fmtString.length();
		
		//find format string in list of constant strings
		strNum = Integer.parseInt(ListOfStrings.get(fmtString).toString());
		
		//append end of string character to format string
		fmtString = fmtString.concat("\\00");
		
		//print first part of call to scanf()
		code.print("%r"+ ssaReg++ + " = call i32 (i8*, ...)* @scanf(i8* getelementptr inbounds ([" +
				(numChars+1) + " x i8]* @.str" + strNum + ", i32 0, i32 0)");
		
		//add args to scanf() call
		for(int i=1;i<fc.getNumArguments();i++)
		{
			String arg = fc.getArgument(i).toString();
			arg = arg.substring(arg.indexOf('&')+2, arg.indexOf('&')+3);
			code.print(", i32* %" + arg);
		}
		
		code.println(")");
		return ssaReg-1;
	}
	
	private int printfCall(FunctionCall fc)
	{
		int strNum;
		
		//get format string arument
		String fmtString = fc.getArgument(0).toString();
		fmtString = fmtString.substring(fmtString.indexOf('"')+1, fmtString.length());
		fmtString = fmtString.substring(0, fmtString.indexOf('"'));
		int numChars = fmtString.length();
		
		//compare to list of available constant strings
		strNum = Integer.parseInt(ListOfStrings.get(fmtString).toString());
		
		//add string terminator character to format string
		fmtString = fmtString.concat("\\00");
		
		int beginReg=0, endReg=-1;
		
		if(fc.getNumArguments() > 1)
			beginReg=ssaReg;
		List<Integer> regsUsed = new ArrayList<Integer>();
		//generate load instructions to load data to be printed into registers
		for(int i=1;i<fc.getNumArguments();i++)
		{
			endReg = ssaReg;
			String arg = fc.getArgument(i).toString();
			String arrayLoc=arg;
			dump.println("arg="+arg);
			arg = arg.substring(arg.indexOf('&')+1, arg.indexOf('&')+2);
			
			if(ListOfArrays.containsKey(arg)){
				code.println("%r" + ssaReg++ +"= getelementptr inbounds "+ListOfArrays.get(arg)+"* %"+arg+", i32 0, i32 "+arrayLoc.substring(arrayLoc.indexOf("[")+1,arrayLoc.indexOf("]")-1));
				arg = Integer.toString(ssaReg-1);
				arg = new String("r"+arg);
			}
				code.println("%r" + ssaReg++ + " = load i32* %" + arg);
				regsUsed.add(ssaReg-1);
		}
		
		//print call to printf()
		code.print("%r"+ ssaReg++ + " = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([" +
				(numChars+1) + " x i8]* @.str" + strNum + ", i32 0, i32 0)");
		
		//add args to printf() call
		for(int i=0;i<=regsUsed.size();i++)
		{
			try{
				code.print(", i32 %r" + regsUsed.get(i));
			}
			catch(Exception e){}
		}
		
		code.println(")");
		return ssaReg-1;
	}
}