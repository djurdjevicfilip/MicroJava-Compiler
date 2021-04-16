package rs.ac.bg.etf.pp1;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.CounterVisitor.VarCounter;
import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;
import java.util.*;
public class SemanticAnalyzer extends VisitorAdaptor {


	int printCallCount = 0;
	int varDeclCount = 0;
	Obj currentMethod = null;
	Obj currentClass = null;
	Obj currentDesignator = Tab.noObj;
	Obj currentMethodDesignator = null;
	boolean returnFound = false;
	boolean errorDetected = false;
	boolean methodReturnFound = false;
	boolean assignable = true;
	boolean zeroParams = true;
	Struct classExtendsType = null;
	int doOpen = 0, switchOpen = 0;
	boolean arrayAccess = false, methodOpen = false;
	int nestedArr = 0;
	int nVars;
	Struct currentVarType = null;
	String currentVarName = "";
	String designatorString = "";
	Struct factorType = null, termType = null;
	Struct methodReturnType = null;
	Obj program = null;
    boolean isArray = false;
	static Struct arrayType = new Struct(Struct.Array);
	static Struct boolType = new Struct(Struct.Bool);
	static Struct classType = new Struct(Struct.Class);

	
	Logger log = Logger.getLogger(getClass());

    // ---------------------- REPORT ----------------------
	
	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" na liniji ").append(line);
		log.error(msg.toString());
	}

	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message); 
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" na liniji ").append(line);
		log.info(msg.toString());
	}

    // ---------------------- HELPER FUNCTIONS ----------------------
	
	private boolean isVariableGlobal(VarX var) {
		SyntaxNode varList = var.getParent();
		SyntaxNode varDecl = varList.getParent();
		Class finalClass = varDecl.getParent().getClass();
		return finalClass.equals(DeclarationVar.class);
	}
	private boolean isImmediateFunctionCall(DesignatorName designatorName) {
		return designatorName.getParent().getClass().equals(DesignatorFunctionCall.class) ||
			   designatorName.getParent().getClass().equals(FactorMethod.class);
	}
	private boolean alreadyDeclared(String name) {
		return Tab.currentScope().findSymbol(name)!=null;
	}
	
	private boolean isInteger(Struct s) {
		if(s==null) return false;
		
		if(s.getKind() == Struct.Array && s.getElemType().getKind() == Struct.Int) {
			return true;
		}
		
		return s.getKind() == Struct.Int;
	}
	
	private boolean typesEquivalent(Struct a, Struct b, boolean isMethod) {
		if(a==null && isMethod && (b.getKind() == Struct.None || b instanceof ClassType || b.getKind() == Struct.Array)) return true;
		if(a == null || b == null) return false;
		if(a instanceof ClassType && b instanceof ClassType) {
			if(((ClassType)a).name.equals(((ClassType)b).name)) {
				return true;
			}else if(ancestor(a,b)) {
				return true;
			}
			else {
				return false;
			}
		}
		if(a.getKind() == Struct.Array && b.getKind() == Struct.Array) {
			return typesEquivalent(a.getElemType(), b.getElemType(), isMethod);
		}
		
		return (a.getKind() == Struct.None && isMethod) || a.getKind() == b.getKind();
	}
	
	private boolean typesCompatible(Struct a, Struct b) {
		if(typesEquivalent(a,b,false)) return true;
		return a.getKind() == b.getKind();
	}
	private boolean parent(Struct potentialParent, Struct potentialChild) {
		return potentialChild.getElemType() == potentialParent;
	}
	private boolean ancestor(Struct potentialAncestor, Struct potentialDescendant) {
		
		if(potentialAncestor == null || potentialDescendant == null) return false;
		if(potentialAncestor.getKind() == Struct.Class && 
				potentialDescendant.getKind() == Struct.Class) {
			if(parent(potentialAncestor, potentialDescendant)) return true;
			
			Struct d = potentialDescendant.getElemType();
		
			if(d==null) return false;
	
			
			return ancestor(potentialAncestor, d);
		}
		
		return false;
	}
	
	private void insertConst(ConstVal constVal, Struct type) {
		ConstAssign constAssign = (ConstAssign) constVal.getParent();
			
		if (type == currentVarType) {
			if (!alreadyDeclared(constAssign.getConstName())) {
				Obj obj = Tab.insert(Obj.Con, constAssign.getConstName(), currentVarType);
				
				// Set value based on the type
				if(type == Tab.intType) {
					obj.setAdr(((ConstantNumber)constVal).getValue());
				}else if(type == Tab.charType) {
					//obj.setAdr(((ConstantChar)constVal).getValue());
				}else if(type == boolType) {
					if (((ConstantBool)constVal).getValue().equals("false"))
						obj.setAdr(0);
					else
						obj.setAdr(1);
				}
			}
			else {
				report_error("Error on line "  + constAssign.getLine() +": already declared - "+ constAssign.getConstName() , null);
			}
		}
		else {
			report_error ("Error on line " + constAssign.getLine() + ": types not the same.", null );
		}
	}

	public boolean passed() {
		return !errorDetected;
	}
	
    // ---------------------- PROGRAM ----------------------
	
	// Program Start
    public void visit(ProgName progName){
    	program = progName.obj = Tab.insert(Obj.Prog, progName.getPName(), Tab.noType);
    	Tab.insert(Obj.Type, "bool", boolType);
    	Tab.insert(Obj.Var, "intArr", Tab.intType);
    	Tab.insert(Obj.Var, "charArr", Tab.charType);
    	Tab.insert(Obj.Var, "boolArr", boolType);
    	
    	Tab.openScope();
    }
    
    // Program End
    public void visit(Program program){
    	
    	nVars = Tab.currentScope.getLocals().symbols().size();
    	
    	Obj obj = Tab.find("main");

    	if(obj.getKind() != Obj.Meth) {
    		report_error ("Error : main method not declared.", null );
    		
    	}
    	Tab.chainLocalSymbols(program.getProgName().obj);
    	Tab.closeScope();
    	
    	
    	
    }

    // ---------------------- CONSTANTS ----------------------
    
	public void visit(ConstantNumber constNum) {
		insertConst(constNum, Tab.intType);
	}
	public void visit(ConstantChar constChar) {
		insertConst(constChar, Tab.charType);
	}
	public void visit(ConstantBool constBool) {
		insertConst(constBool, boolType);
	}
	

    // ---------------------- TYPE ----------------------
	
    public void visit(Type type){
		// Find type in table
		Obj typeNode = Tab.find(type.getTypeName());
		
    	if(typeNode == Tab.noObj){
    		// Type not found
    		report_error("Error on line " + type.getLine() + " - Type " + type.getTypeName() + " not found in the symbol table ", null);
    		type.struct = Tab.noType;
    		
    	}else{
    		if(Obj.Type == typeNode.getKind()){
    			// Is type
    			type.struct = typeNode.getType();
 
    			
    			// If the type refers to a variable/const declaration, update the current variable type
    			SyntaxNode parent = type.getParent();
    			if(parent instanceof VarDeclaration || parent instanceof ConstantDeclaration) {
    				
    			}
    		}else{
    			// Is a word (not a type)
    			report_error("Error on line " + type.getLine() + " " + type.getTypeName() + " is not a type", null);
    			type.struct = Tab.noType;
    		}
    	}
    	currentVarType = typeNode.getType();
    	
    	
		currentVarName = type.getTypeName();
    	// Class ?
    }

    // ---------------------- VARIABLES ----------------------
    
    public void visit(Variable var){
    	if(isVariableGlobal(var))
    		report_info("Global Variable - " + var.getVarName(), null);
    	else
    		report_info("Local Variable - " + var.getVarName(), null);
		if (alreadyDeclared(var.getVarName())) report_error("Error on line "  + var.getLine() +" already declared "+ var.getVarName() , null);
		else {
			Obj obj = Tab.insert(Obj.Var, var.getVarName(), currentVarType);
			obj.setFpPos(-1);
		}
		
		
	}
    
    // Variable Array
    public void visit(VariableArray var){
    	if(isVariableGlobal(var))
    		report_info("Global Variable - " + var.getVarName() + "[]", null);
    	else
    		report_info("Local Variable - " + var.getVarName() + "[]", null);
    	
    	// Array
    	Struct struct = new Struct(Struct.Array);
    	
    	
    	// Array element type
		struct.setElementType(currentVarType); 
		
		if (alreadyDeclared(var.getVarName())) report_error("Error on line "  + var.getLine() +" already declared "+ var.getVarName() , null);
		else {
			Obj obj = Tab.insert(Obj.Var, var.getVarName(), struct);
			obj.setFpPos(-1);
		}
	}
    
    // ---------------------- METHODS ----------------------
     
    // Method start
    public void visit(MethodType methodType) {
    	currentMethod = Tab.insert(Obj.Meth, methodType.getMethName(), methodType.getType().struct);
    	//Tab.insert(Obj.Meth, "this."+methodType.getMethName(), methodType.getType().struct);
    	currentMethod.setLevel(0);
    	
    	report_info("Method detected - "+methodType.getMethName(),null);
    	// Implicit this parameter
    	if(currentClass != null) {
    		currentMethod.setLevel(1);
    	}
    	
    	methodOpen = true;
    	Tab.openScope();
    	methodType.obj = currentMethod;
    	//Virtual table
    	if(partOf(ClassDeclaration.class, methodType)) {

        	Struct type = new Struct(Struct.None);
        	Tab.insert(Obj.Fld, "virtual table", type);
    	}
    }
    private boolean partOf(Class c, SyntaxNode des) {
		SyntaxNode nd = des.getParent();
		if(nd.getClass() == c) {
			return true;
		}
		else if(nd instanceof Program) {
			return false;
		}
		return partOf(c,nd);
	}
    public void visit(MethodVoid methodVoid) {

		
    	currentMethod = Tab.insert(Obj.Meth, methodVoid.getMethName(), Tab.noType);
    	//Tab.insert(Obj.Meth, "this." + methodVoid.getMethName(), Tab.noType);
    	currentMethod.setLevel(0);
    	
    	report_info("Method detected - "+methodVoid.getMethName(),null);

    	// Implicit this parameter
    	if(currentClass != null) {
    		currentMethod.setLevel(1);
    	}

    	methodVoid.obj = currentMethod;
    	
    	methodReturnType = Tab.noType;
    	
    	methodOpen = true;
    	Tab.openScope();

    	
    	//Virtual table
    	if(partOf(ClassDeclaration.class, methodVoid)) {

        	Struct type = new Struct(Struct.None);
        	Tab.insert(Obj.Fld, "virtual table", type);
    	}
    }
    
    // Method end
    public void visit(MethodDeclaration methodDeclaration) {
    	
    	String name = "";
    	if(methodDeclaration.getMethodTypeName() instanceof MethodType)
    		name = ((MethodType) methodDeclaration.getMethodTypeName()).getMethName();
    	else 
    		name = ((MethodVoid) methodDeclaration.getMethodTypeName()).getMethName();
    	
    	
    	
    	if (!methodReturnFound && currentMethod.getType() != Tab.noType) {
    		report_error("Error on line " + methodDeclaration.getLine() + " - "+ name +" method has to have a return statement with an expression!", null);
    	}
    	
    	if(currentMethod.getType() != Tab.noType && !typesEquivalent(currentMethod.getType(), methodReturnType, false)) {
    		report_error("Error on line "+methodDeclaration.getLine()+" - "+ name +" method's return expression type does not match the method type!", null);	
    	}
    	
    	
    	
    	if(currentMethod.getType() == Tab.noType && methodReturnType != Tab.noType) {
    		report_error("Error "+ methodDeclaration.getLine() +" - "+ name +" method's return expression type does not match the method type!", null);	
        	
    	}
    	
    	Tab.chainLocalSymbols(currentMethod);
    	Tab.closeScope();


    	
    	methodOpen = false;
    	currentMethod = null;
    	
    	methodReturnFound = false;
    }
    
    public void visit(StatementReturnExpr statementReturnExpr) {
    	methodReturnFound = true;
    	Expr expr = statementReturnExpr.getExpr();
    	methodReturnType = expr.struct;
    	
    	if(!methodOpen) {
    		report_error("Error - on line " + statementReturnExpr.getLine() +" return cannot be found outside a method", null);
            
    	}
    }
    public void visit(StatementReturn statementReturn) {
    	methodReturnFound = true;
    	methodReturnType = Tab.noType;
    	
    }
    
    LinkedList<String> designators = new LinkedList<String>();
    int designatorsIndex = 0;
    public void visit(DesignatorName designatorName) {
    	
    	zeroParams = true;
    	
    	// Immediate function call
    	if(isImmediateFunctionCall(designatorName)) {
    		if (Tab.find(designatorName.getName()) == Tab.noObj) {
    			report_error("Error - Method - "+ designatorName.getName().toString() +" - is not declared!", null);
    		}

        	Obj obj = Tab.find(designatorName.getName());
        	
        	if(obj.getKind() != Obj.Meth) {
        		report_error("Error on line "+designatorName.getLine()+" - " + designatorName.getName()+" is not a method", null);
        	}
        	report_info("Function Call Detected - "+designatorName.getName(),null);
        	currentMethodDesignator = obj;
    		// Check Formal Parameters ?
    	}
    	
    	Obj obj = Tab.find(designatorName.getName());

    	designatorName.obj = currentDesignator = obj;
    	

    	if(obj.getKind() == Obj.Meth) {
    		assignable = false;
    	}else {
    		assignable = true;
    	}
    	
    	if(designatorName.getName().equals("this")) {
    		designatorName.obj = currentDesignator = currentClass;
    		
    		if(currentClass==null) {
    			report_error("Error on line " + designatorName.getLine() + " - this must be used in a class", null);
    	    	designatorName.obj = currentDesignator = Tab.noObj;
    		}
    	}
    	else if(designatorName.obj == Tab.noObj) {
    		report_error("Error on line " + designatorName.getLine() + " - name "+designatorName.getName().toString() +" - is not declared!", null);
    	}
    	
    	
    	if(designatorName.obj.getType() instanceof ClassType) {
        	designators.add(((ClassType)designatorName.obj.getType()).name);
    	}else {

        	designators.add(designatorName.getName());
    	}
    	designatorsIndex++;

    	if(!(designatorName.getParent() instanceof Designator)) {
    		designatorString = designators.remove(--designatorsIndex);
    	}
    }

    // ---------------------- FORMAL PARAMETERS ----------------------
    
    public void visit(FormalParameterDeclaration formalParameterDeclaration) {
    	if (alreadyDeclared(formalParameterDeclaration.getParam())) report_error("Error on line "  + formalParameterDeclaration.getLine() +" already declared "+ formalParameterDeclaration.getParam() , null);
		else {
			Obj obj = Tab.insert(Obj.Var, formalParameterDeclaration.getParam(), formalParameterDeclaration.getType().struct);
			obj.setFpPos(currentMethod.getLevel());
		}
    	

    	report_info("Formal Parameter Detected - "+formalParameterDeclaration.getParam(),null);
    	
    	// Increment number of formal params
    	currentMethod.setLevel(currentMethod.getLevel()+1);
    	Tab.chainLocalSymbols(currentMethod);
		report_info("FILL "+currentMethod.getLocalSymbols().size(),null);
		
    	//Tab.chainLocalSymbols(Tab.find("this."+currentMethod.getName()));
    }

    // ---------------------- ARRAY ELEMENT ACCESS ----------------------

	public void visit(ArrayEntry arrEntry) {
		nestedArr++;
	}
    public void visit(DesignatorArray designatorArray) {	
    	designatorString = designators.remove(--designatorsIndex);

    	DesignatorName designator = null;
    	DesignatorPoint dp = null;
    	String desStr = "";
    	
    	
    	if(designatorArray.getDesignator() instanceof DesignatorName) {
    		designator = (DesignatorName) designatorArray.getDesignator();
    	
	    	report_info("Array Element Access Detected - "+designator.getName(),null);
	    	Obj obj = Tab.find(designator.getName());
	    	
	    	// Check if it's an array
	    	if(obj.getType().getKind() != Struct.Array) {
	        	report_error("Error on line "+designatorArray.getLine()+" - "+designator.getName()+" is not an array",null);
	    	}
	    	
	    	
	    	int kind = obj.getType().getElemType().getKind();
	    	if(kind == Struct.Int) {
	    		currentDesignator = Tab.find("intArr");
	    	}
	    	else if(kind == Struct.Char) {
	    		currentDesignator = Tab.find("charArr");
	    	}
	    	else if(kind == Struct.Bool) {
	    		currentDesignator = Tab.find("boolArr");
	    	}
	    	else if(kind == Struct.Class) {
	    		ClassType classType = (ClassType) obj.getType().getElemType();
	    		desStr = classType.name;
	    		currentDesignator = Tab.find(classType.name);
	    		
	    		currentDesignator = new Obj(Obj.Elem, currentDesignator.getName(), currentDesignator.getType());
	    	
	    	}
	    	
    	}
	    else {
	    	dp = (DesignatorPoint) designatorArray.getDesignator();
	    	
	    	report_info("Array Element Access Detected - "+designatorString,null);
	    	Obj obj = dp.obj;
	    	// Check if it's an array
	    	if(obj.getType().getKind() != Struct.Array) {
	        	report_error("Error on line "+designatorArray.getLine()+" - "+designatorString+" is not an array",null);
	    	}
	    	report_info("ARRA "+dp.getName(),null);
	    	int kind = obj.getType().getElemType().getKind();
	    	if(kind == Struct.Int) {
	    		currentDesignator = Tab.find("intArr");
	    	}
	    	else if(kind == Struct.Char) {
	    		currentDesignator = Tab.find("charArr");
	    	}
	    	else if(kind == Struct.Bool) {
	    		currentDesignator = Tab.find("boolArr");
	    	}
	    	else if(kind == Struct.Class) {
	    		ClassType classType = (ClassType) obj.getType().getElemType();
	    		
	    		desStr = classType.name;
	    		
	    		
	    		currentDesignator = Tab.find(classType.name);
	    		currentDesignator = new Obj(Obj.Elem, currentDesignator.getName(), currentDesignator.getType());
	    	
	    		
	    	}
	   	}

    
    	arrayAccess = true;
    	// Check expression type
    	Expr expr = designatorArray.getExpr();
    	
    	
    	if(expr.struct.getKind()!=Struct.Int) {
        	report_error("Error on line "+designatorArray.getLine()+" - expression inside brackets is not an integer",null);
    	}
    	
    	designatorString = desStr;
    	designators.add(desStr);
    	designatorsIndex++;
    	
    	nestedArr--;
    	
    	// Remove from the list if there's no element access after this
    	if(!(expr.getParent().getParent() instanceof DesignatorPoint || expr.getParent() instanceof DesignatorArray)) {
   		 currentDesignator = Tab.find(designators.remove(--designatorsIndex));
   	 	}

    	designatorArray.obj = currentDesignator;
    	
    
    }
 
    // ---------------------- ASSIGNMENT ----------------------
    
    public void visit(DesignatorAssignop designatorAssignop) {
    	Designator des = designatorAssignop.getDesignator();
    	Expr expr = designatorAssignop.getExpr();
    	
    	
    	if(expr.struct!=null && des.obj!=null)
    	if(!ancestor(des.obj.getType(), expr.struct) && !(expr.struct.getKind() == Struct.Class && !(expr.struct instanceof ClassType) && des.obj.getType().getKind()==Struct.Array)) {
	    	report_info("" +des.obj.getType().getKind() + " "+expr.struct.getKind(),null);
    		if(!typesEquivalent(des.obj.getType(),expr.struct, false)) {
	    		report_error("Error on line "+expr.getLine()+ " - cannot assign a value of different type ", null);
	    	}
    	}
    	if(des.obj.getKind()==Obj.Con) {
    		report_error("Error on line "+expr.getLine()+ " - cannot assign a value to a constant ", null);
    	}
    	
    	if(des.obj.getKind()==Obj.Meth) {
    		report_error("Error on line "+expr.getLine()+ " - cannot assign a value to a function/method ", null);
    	}
    	
    	/*if(des.obj.getKind()==Obj.Type) {
    		report_error("Error on line "+expr.getLine()+ " - cannot assign a value to a type  ", null);
    	}*/
    }
    
    public void visit(DesignatorAssignOperation designatorAssign) {
 
    	/*if (!assignable) {
        	report_error("Error on line " + designatorAssign.getLine() +" - cannot assign a value", null);
    	}*/
    	assignable = true;
    }
    
    public void visit(DesignatorIncrement designatorInc) {
    	
    	Struct type = currentDesignator.getType();
    	
    	Designator des = designatorInc.getDesignator();
    	if(!assignable || type.getKind() == Struct.Class || (!arrayAccess && type.getKind() == Struct.Array) || des.obj.getType().getKind()!=Struct.Int) {
        	report_error("Error on line "+designatorInc.getLine()+" - cannot inc value", null);
    	}
    	arrayAccess = false;
    	assignable = true;
    }
    
    public void visit(DesignatorDecrement designatorDec) {
    	
    	Struct type = currentDesignator.getType();
    	
    	Designator des = designatorDec.getDesignator();
    	if(!assignable || type.getKind() == Struct.Class || (!arrayAccess && type.getKind() == Struct.Array) || des.obj.getType()!=Tab.intType) {
            	report_error("Error on line "+designatorDec.getLine()+" - cannot dec value", null);
    	}
    	
    	arrayAccess = false;
    	assignable = true;
    }
    
    // ---------------------- INNER CLASS ----------------------
    
    // Start of class
    public void visit(ClassName className) {

    	ClassType struct = new ClassType(Struct.Class, className.getClassName());
    	
    	classExtendsType = null;
    	Obj obj = null;
    	if (alreadyDeclared(className.getClassName())) report_error("Error on line "  + className.getLine() +" already declared "+ className.getClassName() , null);
		else obj = Tab.insert(Obj.Type, className.getClassName(), struct);
    	
    	className.obj = obj;
    	
    	currentClass = obj;
    	report_info("Class Found - "+className.getClassName(),null);
    	
    	Tab.openScope();
    	
    	
    	//Virtual table
    	Struct type = new Struct(Struct.None);
    	Tab.insert(Obj.Fld, "virtual table", type);
    }
    
    public void visit(ClassVarDeclList classVarDeclList) {
    	
    }
    
    // End of class
    public void visit(ClassDeclaration classDeclaration) {
    	
		Tab.chainLocalSymbols(classDeclaration.getClassName().obj);	//members
		
		if(Tab.currentScope.getLocals()!=null) {
		Collection<Obj> locals = Tab.currentScope.getLocals().symbols();

		if(classExtendsType != null) {
			classDeclaration.getClassName().obj.getType().setElementType(classExtendsType);
			
			if(classExtendsType instanceof ClassType) {
				ClassType classType = (ClassType) classExtendsType;
				
				//Extended obj
				Obj obj = Tab.find(classType.name);
				
				Collection<Obj> localSyms = obj.getLocalSymbols();
		    	//Tab.closeScope();
		    	

				Tab.closeScope();
				
				// Add extended class to globalScope
				/*for (Iterator iterator = localSyms.iterator(); iterator.hasNext();) {
					Obj ob = (Obj) iterator.next();
					
					Obj added = Tab.insert(ob.getKind(), classDeclaration.getClassName().getClassName()+"."+ob.getName(), ob.getType());
						
					// Add formal parameters
					if(added!=null) {
						Collection<Obj> formals = ob.getLocalSymbols();
						Tab.openScope();
						
						for (Iterator iterator2 = formals.iterator(); iterator2.hasNext();) {
							Obj obj2 = (Obj) iterator2.next();
							// Check if it's a formal parameter
							if(obj2.getFpPos()!=-1)
								Tab.insert(obj2.getKind(),obj2.getName(),obj2.getType());
						}
						
						Tab.chainLocalSymbols(added);
						Tab.closeScope();
					}
				}

				for (Iterator iterator = locals.iterator(); iterator.hasNext();) {
					Obj ob = (Obj) iterator.next();
					Obj added = Tab.insert(ob.getKind(), classDeclaration.getClassName().getClassName()+"."+ob.getName(), ob.getType());
					

					// Add formal parameters
					if(added!=null) {
						Collection<Obj> formals = ob.getLocalSymbols();
						Tab.openScope();
						
						for (Iterator iterator2 = formals.iterator(); iterator2.hasNext();) {
							Obj obj2 = (Obj) iterator2.next();
							// Check if it's a formal parameter
							if(obj2.getFpPos()!=-1)
								Tab.insert(obj2.getKind(),obj2.getName(),obj2.getType());
						}
						
						Tab.chainLocalSymbols(added);
						Tab.closeScope();
					}
				}*/
			}
		}else {
	    	//Tab.chainLocalSymbols(classDeclaration.getClassName().obj);
	    	Tab.closeScope();
			
			/*for (Iterator iterator = locals.iterator(); iterator.hasNext();) {
				Obj obj = (Obj) iterator.next();
				Obj added = Tab.insert(obj.getKind(), classDeclaration.getClassName().getClassName()+"."+obj.getName(), obj.getType());

				// Add formal parameters
				if(added!=null) {
					Collection<Obj> formals = obj.getLocalSymbols();
					Tab.openScope();
					
					for (Iterator iterator2 = formals.iterator(); iterator2.hasNext();) {
						Obj obj2 = (Obj) iterator2.next();
						// Check if it's a formal parameter
						if(obj2.getFpPos()!=-1)
							Tab.insert(obj2.getKind(),obj2.getName(),obj2.getType());
					}
					
					Tab.chainLocalSymbols(added);
					Tab.closeScope();
				}
			}*/
		}
		
		if(classExtendsType == classDeclaration.getClassName().obj.getType()) {
			report_error("Error on line "  + classDeclaration.getLine() +" class cannot extend itself ", null);
    		
		}

		}
		
		currentClass = null;
    }
    
    public void visit(ClassExtendsTrue classExtendsS) {
    	Type type = classExtendsS.getType();
    	
    	classExtendsType = type.struct;
    	if(type.struct.getKind()!=Struct.Class) {
    		report_error("Error on line "  + classExtendsS.getLine() +" must extend a class type ", null);
    		
    	}
    	else {
    	ClassType classType = (ClassType) classExtendsType;
		
		Obj obb = Tab.find(classType.name);
		
		Collection<Obj> localSyms = obb.getLocalSymbols();
		
		// Add to local scope from extended class
		for (Iterator iterator = localSyms.iterator(); iterator.hasNext();) {
			Obj ob = (Obj) iterator.next();
			
		
			Obj added = Tab.insert(ob.getKind(), ob.getName(), ob.getType());
			// Add formal parameters
			if(added!=null) {
				Collection<Obj> formals = ob.getLocalSymbols();
				Tab.openScope();
				
				for (Iterator iterator2 = formals.iterator(); iterator2.hasNext();) {
					Obj obj2 = (Obj) iterator2.next();
					
					// Check if it's a formal parameter
					if(obj2.getFpPos()!=-1)
						Tab.insert(obj2.getKind(),obj2.getName(),obj2.getType());
				}
				
				Tab.chainLocalSymbols(added);
				Tab.closeScope();
			}
		}
    	}
		Tab.chainLocalSymbols(currentClass);
		
		//Tab.openScope();
    }
    
    // ---------------------- INSTANTIATE OBJECT ----------------------
    
    public void visit(FactorNew factorNew) {
    	Type type = factorNew.getType();
    	
    	String name = type.getTypeName().toString();
    	
    	Obj obj = Tab.find(name);

    	factorType = obj.getType();
    	
    	if(obj.getType().getKind() == Struct.Class) {
        	report_info("Object creation - "+name,null);
    	}
    	
    	Struct struct = factorType;
    	
    	if(isArray) {
    		struct = new Struct(Struct.Array, factorType);
    	}

    	
    	factorNew.struct = struct;

    }
    
    public void visit(OptionalExpression optExpr) {
    	isArray = true;
    	Expr expr = optExpr.getExpr();
    	
    	if(expr.struct.getKind()!=Struct.Int) {
    		report_error("Error on line "  + expr.getLine() +" expression inside brackets must be integer " , null);
    		
    	}
    	
    }
    public void visit(NoOptionalExpression noopt) {
    	isArray = false;
    }
    // ---------------------- CLASS FIELDS ----------------------
      
    public void visit(ClassVariable var){

    	
    	ClassType struct = new ClassType(currentVarType.getKind(), currentVarName);
    	
    	struct.setElementType(currentVarType.getElemType());
    	var.struct = struct;
    	report_info("Class field - " + var.getVarName() + " - in class " + currentClass.getName() , null);
		if (alreadyDeclared(var.getVarName())) report_error("Error on line "  + var.getLine() +" already declared "+ var.getVarName() , null);
		else {
			Tab.insert(Obj.Fld, var.getVarName(), struct);
			//Tab.insert(Obj.Fld, "this."+var.getVarName(), struct);
		}
	}
     
     public void visit(ClassVariableArray var){
    	ClassType struct = new ClassType(Struct.Array, currentVarName);
    	report_info("Class field - " + var.getVarName() + " - in class " + currentClass.getName() , null);
    	report_info("CLAS  "+struct.getKind(),null);
    	// Array element type
		struct.setElementType(currentVarType); 
		var.struct = struct;
		if (alreadyDeclared(var.getVarName())) report_error("Error on line "  + var.getLine() +" already declared "+ var.getVarName() , null);
		else {
			Tab.insert(Obj.Fld, var.getVarName(), struct);
			//Tab.insert(Obj.Fld, "this."+var.getVarName(), struct);
		}
	}

    // ---------------------- CLASS FIELD ACCESS ----------------------
    
    public void visit(DesignatorPoint designatorPoint) {
    	
    	// Check if we are accessing a class
    	
    	if(currentDesignator!=null) {
	    	// Sta ako se pristupa bas toj klasi
	    	if(currentDesignator.getType().getKind() != classType.getKind()) {
	    		report_error("Error on line "  + designatorPoint.getLine() +" not a class type - " + designatorString, null);
	    	}
	    	Struct struct = currentDesignator.getType();
	    	String className = "";
	    	
	    	if(struct instanceof ClassType) {
	    		className = ((ClassType) struct).name;
	    	}
	    	
	    	
	    	
	    	Obj obj = null;
	    	
	    	if(currentDesignator==currentClass) {
	    		// This parameter
	    		//obj = Tab.find("this."+designatorPoint.getName());
	    		
	    		Collection<Obj> objs = Tab.currentScope().values();
	    		
	    		
	    		Tab.closeScope();
	    		
	    		obj = Tab.find(designatorPoint.getName());

	    		report_info("NAME "+designatorPoint.getName(),null);
	    		
	    		Tab.openScope();

	    		for (Iterator iterator = objs.iterator(); iterator.hasNext();) {
					Obj object = (Obj) iterator.next();
					Tab.insert(object.getKind(),object.getName(),object.getType());
				}
	    		if(obj.getKind()!=Obj.Fld && obj.getKind() != Obj.Meth) {
	    			report_error("Error on line "  + designatorPoint.getLine() +" field - " + designatorPoint.getName() +" is not a member of "+className, null);
	            	
	    		}
	    	}else {
	    		//obj = Tab.find(className + "." + designatorPoint.getName());
	    		obj = Tab.find(className);

	    		report_info("NAME "+designatorPoint.getName(),null);
	    		Collection<Obj> locals = obj.getLocalSymbols();
	    		
	    		for (Iterator iterator = locals.iterator(); iterator.hasNext();) {
					Obj object = (Obj) iterator.next();
					if(object.getName().contentEquals(designatorPoint.getName())) {
						obj = object;
						break;
					}
				}
	    	}
	    	// Field or method
	    	String typ = "field";
	    	if(obj.getKind() == Obj.Meth) {
	    		assignable = false;
	    		currentMethodDesignator = obj;
	    		typ = "method";
	    	}
	
	    	report_info("Class " + typ + " access - " + designatorPoint.getName() + " - in class "+ className , null);
	    	
	    	if(obj==Tab.noObj) {
	    		report_error("Error on line "  + designatorPoint.getLine() +" field - " + designatorPoint.getName() +" is not a member of "+className, null);
	        	
	    	}
	    	
	    	struct = obj.getType();
	    	if(struct instanceof ClassType) {
	    		className = ((ClassType) struct).name;

		    	designatorString += "." + className;
	    	}
	    	else {

		    	designatorString += "." + designatorPoint.getName();
	    	}
	    	report_info("objjjj "+obj.getType().getKind(),null);
	    	designatorPoint.obj = obj;
	    
	    	designators.set(designatorsIndex-1, designators.get(designatorsIndex-1) + "." + designatorPoint.getName());
	    	
	    	currentDesignator = designatorPoint.obj;
	    	
	    	if(!(designatorPoint.getParent() instanceof Designator)) {
	    		designatorString = designators.remove(--designatorsIndex);
	    	}
    	}
    }
    // ---------------------- CLASS METHOD ACCESS ----------------------

    // ---------------------- TERMS ----------------------
    
    public void visit(TermBody termBody) {
    	Factor f = termBody.getFactor();
    	
    	termBody.struct = f.struct;
    	
    	if(f.struct!=null && f.struct.getKind() != Struct.Int) {
    			report_error("Error on line "+termBody.getLine()+" - Term factor is not an integer", null);
    	}
    	
    }
    public void visit(TermEnd termEnd) {
    	Factor f = termEnd.getFactor();
    	
    	termEnd.struct = f.struct;
    	
    	if(termEnd.getParent().getClass() == TermBody.class) {
    		if(!isInteger(f.struct)) {
    			report_error("Error on line "+termEnd.getLine()+" - TermList factor is not an integer ", null);
    		}
    	}
    }
    public void visit(TermListBody termBody) {
    	Term f = termBody.getTerm();
    	
    	termBody.struct = f.struct;
    	
    	if(!isInteger(f.struct)) {
    		report_error("Error on line "+termBody.getLine()+" - TermList factor is not an integer", null);
    	}
    	
    }
    public void visit(TermListEnd termEnd) {
    	Term f = termEnd.getTerm();

    	termEnd.struct = f.struct;
    	
    	if(termEnd.getParent().getClass() == TermListBody.class) {
    		if(!isInteger(f.struct)) {
    			report_error("Error on line " + termEnd.getLine() + " - Term factor is not an integer ", null);
    		}
    	}
    }
    

    // ---------------------- EXPRESSION ----------------------
    
    public void visit(Expression expr) {
    	Expr1 expr1 = expr.getExpr1();

    	 expr.struct = expr1.struct;
    	 
    }
    
    public void visit(Expression1 expr1) {
    	TermList tl = expr1.getTermList();
    	expr1.struct = tl.struct;
    }
    
    public void visit(Expression1Hyphen expr1) {
    	TermList tl = expr1.getTermList();
    	expr1.struct = tl.struct;
    	  
    	if(!isInteger(tl.struct)) {
    		report_error("Error on line "+expr1.getLine()+" - must be an int type ", null);
    	}
    	
    }
    
    public void visit(ExpressionList exprList) {
    	Expr1 expr1 = exprList.getExpr11();
    	Expr1 exprL = exprList.getExpr1();
    	
    	Relop relop = exprList.getRelop();
    	
    	if(expr1.struct.getKind() != exprL.struct.getKind()) {

    		report_error("Error on line "+exprList.getLine()+ " - type mismatch ", null);
    	}

    	if(expr1.struct.getKind() == Struct.Array || expr1.struct.getKind() == Struct.Class) {
    		if(!(relop instanceof RelopEquals || relop instanceof RelopDoesNotEqual)) {

        		report_error("Error on line "+exprList.getLine()+ " - can't use these relational operators with classes or arrays ", null);
    		}
    	}
    	exprList.struct = boolType;
    }
    
    public void visit(ExpressionListEnd exprList) {
    	Expr1 ele = exprList.getExpr1();
    	exprList.struct = ele.struct;

    }
    // ---------------------- FACTORS ----------------------
    
    public void visit(FactorDesignator factorDesignator) {
    	
    	factorDesignator.struct =  currentDesignator.getType();
    }
    public void visit(FactorNumber factorNumber) {
    	factorNumber.struct = Tab.intType;
    }
    public void visit(FactorChar factorChar) {
    	factorChar.struct = Tab.charType;
    }
    public void visit(FactorBool factorBool) {
    	factorBool.struct = boolType;
    }
    public void visit(FactorExpr factorExpr) {
    	// TODO Expr type
    	factorExpr.struct = factorExpr.getExpr().struct;
    }
    public void visit(FactorMethod factorMethod) {
    	// TODO Check parameters
    	
    	if(currentMethodDesignator!=null) {
	    	factorMethod.struct = currentMethodDesignator.getType();
	    	Collection<Obj> col = currentMethodDesignator.getLocalSymbols();

	    	boolean pass = true;	
	    	
		    for (Iterator iterator = col.iterator(); iterator.hasNext();) {
				Obj formPar = (Obj) iterator.next();
				
				if(formPar.getType().getKind()==Struct.None) pass = false;
				break;
		    }
	    	
	    	
	    	
	    	if(col.size() > 0 && zeroParams && pass) {
	    		
	    		report_error("Error on line "+factorMethod.getLine()+ " - actual parameters do not match the formal parameters", null);
	    	    
	    	}
	    	
	    	currentDesignator = currentMethodDesignator;
    	}
    	
    } 
    
    // ---------------------- TERNARY ----------------------
    
    public void visit(ExpressionTern expr) {
    	
    	Expr1 leftExpr = expr.getLeftExpr().getExpr1();
    	Expr1 rightExpr = expr.getRightExpr().getExpr1();
    	
    	Condition cond = expr.getTernaryStart().getCondition();
    	
    	if(cond.struct != boolType) {
    		report_error("Error on line "+expr.getLine()+ " - condition must be a boolean ", null);
        	
    	}
    	
    	if(leftExpr.struct != rightExpr.struct) {

    		report_error("Error on line "+expr.getLine()+ " - type mismatch ", null);
    				
    	}
    	
    	expr.struct = leftExpr.struct;
    	
    }
    // ---------------------- ACTUAL PARAMETERS ----------------------
    
    public void visit(DesignatorFunctionCall designatorFunctionCall) {
    	
    	if(currentMethodDesignator!=null) {
	    	Collection<Obj> col = currentMethodDesignator.getLocalSymbols();

	    	boolean pass = true;	
	    	
		    for (Iterator iterator = col.iterator(); iterator.hasNext();) {
				Obj formPar = (Obj) iterator.next();
				
				if(formPar.getType().getKind()==Struct.None) pass = false;
				break;
		    }
	    	
	    	if(col.size() > 0 && zeroParams && pass) {
	    		report_error("Error on line "+designatorFunctionCall.getLine()+ " - actual parameters do not match the formal parameters", null);
	    	    
	    	}
	    	
	    	currentDesignator = currentMethodDesignator;
    	}
    }
    List<Struct> actualParameters;
    public void visit(ActParameters actParameters) {

    	Expr expr = actParameters.getExpr();
   
    	actualParameters.add(expr.struct);
    }
   
    public void visit(ActParametersEnd actParametersEnd) {

    	Expr expr = actParametersEnd.getExpr();
    	
    	actualParameters = new ArrayList<>();
    	
    	
    	
    	actualParameters.add(expr.struct);
    }
    
    public void visit(DesignatorActParameters actParameters) {
    	
    	if(currentMethodDesignator!=null) {

    	Collection<Obj> col = currentMethodDesignator.getLocalSymbols();
    	
    	int i = 0;
    	
    	
    	
    	zeroParams = false;
    	
    	boolean isOk = true;

    	int size = 0;
    	for (Iterator iterator = col.iterator(); iterator.hasNext();) {
			Obj formPar = (Obj) iterator.next();
			if(formPar.getFpPos() == -1) continue;
			size++;
		}
    	
    	
    	if(currentClass!=null) {
    		report_info("CUAUSUAU ",null);
    		actualParameters.add(0, null);
    	}
    	
    	
    	if (size != actualParameters.size()) {
    		isOk = false;
    	}
	    	for (Iterator iterator = col.iterator(); iterator.hasNext();) {
				Obj formPar = (Obj) iterator.next();
				if(formPar.getFpPos() == -1) continue;
				try {
				Struct actParType = actualParameters.get(i);
				if(formPar.getType().getKind()==Struct.None) { isOk = true;i++; continue;}
				
				if(!ancestor(formPar.getType(),actParType)&&!typesEquivalent(actParType,formPar.getType(), true)) {
				
					isOk = false;
				}

				}catch(Exception e) {}
				i++;
				
	    	}
    	
    	if(!isOk) {
    		report_error("Error on line "+actParameters.getLine()+ " - actual parameters do not match the formal parameters", null);
    	}
    	}
    }

    // ---------------------- STATEMENTS ----------------------
    
    public void visit(DoIdentifier doIdentifier) {
    	doOpen++;
    }
    
    public void visit(StatementDoWhile statementDoWhile) {
    	doOpen--;
    }
    
    public void visit(SwitchIdentifier switchIdentifier) {
    	switchOpen++;
    }
    
    public void visit(StatementSwitch statementSwitch) {
    	switchOpen--;
    }
    
    public void visit(StatementBreak statementBreak) {
    	if(doOpen==0 && switchOpen==0) {
    		report_error("Error on line "+statementBreak.getLine()+ " - break can only be inside do while or switch statements", null);
    	    
    	}
    }

    public void visit(StatementContinue statementContinue) {
    	if(doOpen==0) {
    		report_error("Error on line "+statementContinue.getLine()+ " - continue can only be inside do while stataments", null);
    	    
    	}
    }
    
    public void visit(StatementRead statementRead) {
    	Struct type = currentDesignator.getType();
    	
    	if(!assignable || type.getKind() == Struct.Class || (!arrayAccess && type.getKind() == Struct.Array)) {
    		report_error("Error on line "+statementRead.getLine()+ " - read designator not ok", null);
     	   
    	}
    	arrayAccess = false;
    }
    
    public void visit(StatementPrint statementPrint) {

    	Struct type = currentDesignator.getType();
    	
    	
    	boolean accessingArray =  arrayAccess && type.getKind() == Struct.Array;
    	
    	if((!accessingArray && !(type.getKind() == Struct.Int || type.getKind() == Struct.Char || type.getKind() == Struct.Bool))) {
    		report_error("Error on line "+statementPrint.getLine()+ " - print expression not ok", null);
      	   
    	}
    	
    	arrayAccess = false;
    }

    // ---------------------- CONDITIONS ----------------------
    
    public void visit(CondFactCompare condFact) {
    	Struct s = null;
    	
    	if(condFact.getExprList() instanceof ExpressionList)
    		s = ((ExpressionList) condFact.getExprList()).struct;
    	else
    		s = ((ExpressionListEnd) condFact.getExprList()).struct;
    	
    	condFact.struct = s;
    }
    
    public void visit(ConditionFactList condFactList) {
    	 CondFactList cfl = condFactList.getCondFactList();
    	 CondFact cf = condFactList.getCondFact();
    	 
    	 if(cf.struct != cfl.struct) {
    			report_error("Error on line "+condFactList.getLine()+ " - conditions not ok", null);
    	 }
    	 
    	 condFactList.struct = boolType;
    }

    public void visit(ConditionFactListEnd condFactList) {

   	 	CondFact cf = condFactList.getCondFact();
   	 	condFactList.struct = cf.struct;
    }
    
    public void visit(CondTerm condTerm) {
    	Struct s = null;
    	
    	if(condTerm.getCondFactList() instanceof ConditionFactList)
    		s = ((ConditionFactList) condTerm.getCondFactList()).struct;
    	else
    		s = ((ConditionFactListEnd) condTerm.getCondFactList()).struct;
    	
    	
    	condTerm.struct = s;
    }
    
    public void visit(ConditionTermList condTermList) {
    	 CondTermList cfl = condTermList.getCondTermList();
    	 CondTerm cf = condTermList.getCondTerm();
    	 
    	 if(cf.struct != cfl.struct) {
    			report_error("Error on line "+condTermList.getLine()+ " - conditions not ok", null);
    	 }
    	 
    	 condTermList.struct = boolType;
    } 

    public void visit(ConditionTermListEnd condTermList) {

   	 	CondTerm cf = condTermList.getCondTerm();
   	 	condTermList.struct = cf.struct;
    }
    public void visit(Condition condition) {
    	Struct s = null;
    	
    	if(condition.getCondTermList() instanceof ConditionTermList)
    		s = ((ConditionTermList) condition.getCondTermList()).struct;
    	else
    		s = ((ConditionTermListEnd) condition.getCondTermList()).struct;
    	
    	
    	condition.struct = s;
    }

    public void visit(IfCondition ifCondition) {
    	Condition cond = ifCondition.getCondition();

    	if(cond.struct.getKind() != Struct.Bool) {
			report_error("Error on line "+ifCondition.getLine()+ " - condition not ok", null);
    	}
    	
    }
    public void visit(WhileCondition doCondition) {
    	Condition cond = doCondition.getCondition();
    	
    	if(cond.struct.getKind() != Struct.Bool) {
			report_error("Error on line "+doCondition.getLine()+ " - condition not ok", null);
    	}
    	
    }

    // ---------------------- SWITCH ----------------------
    List<Integer> switchList;
    
    public void visit(SwitchExpression switchExpression) {
    	switchList = new ArrayList<>();
    	Expr expr = switchExpression.getExpr();
    	
    	if(expr.struct.getKind() != Struct.Int) {

			report_error("Error on line "+switchExpression.getLine()+ " - switch expression type must be int", null);
    	}
    }
    
    public void visit(SwitchElementTrue switchElement) {
    	int num = switchElement.getSwitchElementStart().getNumber();
    	
    	if(switchList.contains(num)) {
    		report_error("Error on line "+switchElement.getLine()+ " - switch cases contain the same integers", null);
    	    
    	}
    	
    	switchList.add(num); 
    }

}