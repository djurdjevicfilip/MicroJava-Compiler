package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.CounterVisitor.FormParamCounter;
import rs.ac.bg.etf.pp1.CounterVisitor.VarCounter;
import rs.ac.bg.etf.pp1.MethodVisitor.ClassMethodVisitor;
import rs.ac.bg.etf.pp1.MethodVisitor.ClassVarNewVisitor;
import rs.ac.bg.etf.pp1.MethodVisitor.ClassVarVisitor;
import rs.ac.bg.etf.pp1.MethodVisitor.ClassVisitor;
import rs.ac.bg.etf.pp1.ast.*;

import rs.etf.pp1.symboltable.concepts.*;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.mj.runtime.Code;
class Patch {
	public int pc;
	public String type;
	public int level;
	public Patch(int pc, String type, int level) {
		this.pc = pc;
		this.type = type;
		this.level = level;
	}
}
public class CodeGenerator extends VisitorAdaptor{

	private int mainPc = 0, varSize = 0;
	private int operation = -1;
	private Obj currentDesignator = null;
	private String newClassLoad = null;
	private boolean invokeVirtual = false;
	String leftEnd = "";
	String designatorNameStr = "";
	ClassMethodVisitor cms = null;
	private boolean designatorIsRight = false, minusPresent = false, arrayAlloc = false, arrayLeft = false;
	private int nestedArr = 0;
	private List<Integer> doReturn = new ArrayList<Integer>();
	Logger log = Logger.getLogger(getClass());

	List<String> classVarNames = null;
	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message); 
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" na liniji ").append(line);
		log.info(msg.toString());
	}
	
	private boolean partOfArray(SyntaxNode des) {
		SyntaxNode node = des.getParent();
		
		if(node instanceof DesignatorArray) {
			return true;
		}
		else if(!(node instanceof DesignatorName || node instanceof DesignatorPoint)) {
			return false;
		}
		return partOfArray(node);
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
	private boolean partOfClass(SyntaxNode des) {
		SyntaxNode node = des.getParent();
		
		if(node instanceof DesignatorPoint) {
			return true;
		}
		else if(!(node instanceof DesignatorName || node instanceof DesignatorArray)) {
			return false;
		}
		return partOfClass(node);
	}
	
	private boolean partOfIncOrDec(SyntaxNode des) {
		SyntaxNode node = des.getParent();
		
		if(node instanceof DesignatorPoint) {
			return true;
		}
		else if(!(node instanceof DesignatorName || node instanceof DesignatorArray)) {
			return false;
		}
		return partOfIncOrDec(node);
	}
	private boolean loadCondition(SyntaxNode syntaxNode) {
		return partOf(StatementPrint.class, syntaxNode)||
		partOf(DesignatorActParameters.class, syntaxNode)||
		partOf(IfCondition.class, syntaxNode)||
		partOf(WhileCondition.class, syntaxNode)||
		partOf(SwitchExpression.class, syntaxNode)||
		partOf(StatementReturnExpr.class, syntaxNode)||
		partOf(DesignatorPoint.class, syntaxNode);
	}
	
	private boolean parentIsMethod(Designator designator) {
		return  designator.getParent() instanceof FactorMethod || (designator.getParent() instanceof DesignatorFunctionCall);
	}
	
	private boolean isCompleteIfElse(SyntaxNode sn) {
		return sn.getParent() instanceof UnmatchedStmt;
	}
	// Returns patch index, otherwise -1
	// If level is -1 it does not check it
	// For now, levels only mean something when paired with if/if_else constructs
	private ArrayList<Integer> patchesContain(String s, int level) {
		int ind = 0;
		ArrayList<Integer> list = new ArrayList<>();
		for(Patch patch: patches) {
			
			if(patch.level == level || level == -1) {
				String[] types = patch.type.split(",");
				for(String type: types) {
					if(type.replaceAll("\\s+","").contentEquals(s)) {
						list.add(ind);
						break;
					}
				}
			}
			ind++;
		}
		return list;
	}
	
	private void patchUp(String type, int level) {
		List<Integer> list = patchesContain(type, level);
		for(int patch: list) {
			Patch p = patches.get(patch);
			Code.fixup(p.pc);
		}
		Collections.reverse(list); 
	    for(Integer index : list){
	        patches.remove((int)index);
	    }
	}
	
	private class Put{
		public int code, val;
		public int placeAfter;
		public String type, name;
		public Obj obj;
		public boolean isPut4 = false;
		public Put(int code, int placeAfter, String type) {
			this.code = code;
			this.placeAfter = placeAfter;
			this.type = type;
		}
		
		public Put(Put p) {
			this.code = p.code;
			this.obj = p.obj;
			this.type = p.type;
			this.val = p.val;
		}
	}
	
	
	private void putList(int code, String type) {
		if(codePutList.size()>0) {
			if(type=="code")codePutList.get(codePutList.size()-1).add(new Put(code, codePutList.size()-1, "code"));
			else if(type=="val") {
				Put p = new Put(code, codePutList.size()-1,"val");
				p.val = code;
				
				codePutList.get(codePutList.size()-1).add(p);
			}
			
		}
	}

	
	private void putListPrev(int code, String type) {
		if(codePutList.size()>0) {
			if(type=="code")codePutList.get(codePutList.size()-1).add(new Put(code, codePutList.size()-2, "code"));
			else if(type=="val") {
				Put p = new Put(code, codePutList.size()-2,"val");
				p.val = code;
				
				codePutList.get(codePutList.size()-1).add(p);
			}
			
		}
	}
	private void putList(Obj obj) {
		if(codePutList.size()>0) {
			Put p = new Put(0, codePutList.size()-1, "obj");
			p.obj = obj;
			codePutList.get(codePutList.size()-1).add(p);
		}
	}
	private void putListName(String s) {
		if(codePutList.size()>0) {
			Put p = new Put(0, codePutList.size()-1, "name");
			
			p.name = s;
			
			codePutList.get(codePutList.size()-1).add(p);
		}
	}
	private void putList(Put p) {
		if(codePutList.size()>0) {
			codePutList.get(codePutList.size()-1).add(p);
		}
	}
	private List<ArrayList<Put>> codePutList = new ArrayList<ArrayList<Put>>();
    // ---------------------- VIRTUAL TABLE UTILS ----------------------
	
	private int classVars = 1;
	
	private HashMap<String, Integer> tvfAddresses = new HashMap<String,Integer>();

	private HashMap<String, Integer> methodAddresses = new HashMap<String,Integer>();
	
	
	//!!! ???
	private void removeByLevel(int level) {
		
	}
	public int getMainPc() {
		return mainPc;
	}
	
	public void visit(ProgName pname) {
		codePutList.add(new ArrayList<Put>());
	}
	
    // ---------------------- ASSIGN ----------------------
	
	public void visit(DesignatorAssignop assign) {
		codePutList.set(codePutList.size()-1, new ArrayList<>());
		// If is class
					if(newClassLoad != null) {
						//Code.put(Code.dup);
						//Code.load(assign.getDesignator().obj);
						//report_info(newClassLoad, null);
						
						Code.loadConst(tvfAddresses.get(newClassLoad));
						
						Code.put(Code.putfield);
						Code.put(0);
						Code.put(0);
					}
		if(leftEnd.contentEquals("array_int")) {
			Code.put(Code.astore);
		}else if(leftEnd.contentEquals("array_not_int")) {
			Code.put(Code.bastore);
		}else{
		
			
			Code.store(assign.getDesignator().obj);
		}
		newClassLoad = null;
		addTwice = null;
		designatorIsRight = false;
		arrayEnt = false;
		
		//Code.fixup(patches.get(patches.size()-1).pc);
	}
	
	public void visit(DesignatorAssignOperation assignop) {
		codePutList.set(codePutList.size()-1, new ArrayList<>());
		designatorIsRight = true;
		arrayEnt = true;
	}
	public void visit(ConstantNumber constNum) {
		Code.loadConst(constNum.getValue());
	}
	
	private boolean partOfArrayBrackets(SyntaxNode sn) {
		while(!(sn instanceof Program)) {
			if(sn instanceof Expression && sn.getParent() instanceof DesignatorArray) {
				return true;
			}
			if(sn instanceof Expression) return false;
			sn = sn.getParent();
		}
		return false;
	}
	
	
	List<Put> paramPutList = new ArrayList<Put>();
	
	public void visit(FactorNumber factorInt) {

		Code.loadConst(factorInt.getN1());
		
		if(partOf(DesignatorActParameters.class,factorInt)) {
			
			Put p = new Put(factorInt.getN1(),0,"val");
			p.val = factorInt.getN1();
			if(!partOf(StatementPrint.class, factorInt)&&!partOf(IfCondition.class,factorInt))
			paramPutList.add(p);
			
		}else {
			if(!partOf(StatementPrint.class, factorInt)&&!partOf(IfCondition.class,factorInt))
			putList(factorInt.getN1(), "val");
			}
		
	}
	public void visit(FactorBool factorBool) {
		Code.loadConst(factorBool.getB1().contentEquals("true")?1:0);
	}
	Obj addTwice = null;
	boolean isClass = false;
	int patchAdr = -1;
	Obj currentClassDesignator = null;
	boolean thisMarker = false;
	List<ArrayList<Obj>> prevDesignators = new ArrayList<ArrayList<Obj>>();
	
	private boolean prevRemoveCondition(SyntaxNode designator) {
		SyntaxNode sn = designator.getParent();
		return !(sn instanceof DesignatorName || sn instanceof DesignatorPoint || sn instanceof DesignatorArray || sn instanceof FactorMethod || sn instanceof DesignatorFunctionCall);
	}
	
	
	private void fillPutList(List<Obj> objs) {
		if(codePutList.size()>0) {
			
			
			
			for (Iterator iterator = objs.iterator(); iterator.hasNext();) {
				Obj obj = (Obj) iterator.next();
				
				putList(obj);
			}
		}
		
	}
	public void visit(StatementRead rd) {
		Code.put(Code.read);
		Code.store(currentDesignator);
	}
	public void visit(DesignatorName designatorName) {
		
		
		
		if(prevRemoveCondition(designatorName)&&prevDesignators.size()>0) {
			List<Obj> objs = prevDesignators.remove(prevDesignators.size()-1);
			
			//fillPutList(objs);
			
		}
		prevDesignators.add(new ArrayList<Obj>());
		currentDesignator = designatorName.obj;
		//thisMarker = false;
		
		
		if(!parentIsMethod(designatorName)) {

			arrayMethodCall = false;
			
			if(!(designatorName.getParent() instanceof Designator) && codePutList.size()==1) {
				codePutList.set(0, new ArrayList<>());
			}
		}
		
		
		if(designatorName.getName().contentEquals("len") || designatorName.getName().contentEquals("ord")||designatorName.getName().contentEquals("read")) {
		
		}else {
			
			
			invokeVirtual = false;
			thisMarker = false;
			
			if(desPointBefore) {
				invokeVirtual = true;
			}
			desPointBefore = false;
			
			if(designatorName.getName().contentEquals("this") ) {
				// THIS
				thisMarker = true;
				if(!parentIsMethod(designatorName)) {
					
					Code.put(Code.load);
					Code.put(0);

					if(!partOf(StatementPrint.class, designatorName)) {
					putList(Code.load,"code");
					putList(0, "code");}
				}
				else if(partOf(FactorMethod.class,designatorName)||partOf(DesignatorFunctionCall.class,designatorName))
				{
					
					Code.put(Code.load);
					
					Code.put(0);

					if(!partOf(StatementPrint.class, designatorName)) {
					putList(Code.load,"code");
					putList(0, "code");
					}
				}
				
				
			}
			else if(partOf(ClassDeclaration.class, designatorName) && (parentIsMethod(designatorName)||!classVarNames.contains(designatorName.getName()))) {
				
				// Without this, but is still a class function
				thisMarker = invokeVirtual = false;
				if(partOf(FactorMethod.class,designatorName)||partOf(DesignatorFunctionCall.class,designatorName))
				{
				Code.put(Code.load);
				Code.put(0);
				}
				Code.put(Code.load);
				Code.put(0);

				if(!partOf(StatementPrint.class, designatorName)) {
				putList(Code.load,"code");
				putList(0, "code");
				}
				thisMarker = true;
				
				invokeVirtual = true;
			}
			if(designatorName.getName().contentEquals("this")) {thisMarker=true;}
			//report_info(" "+designatorName.getName()+ " "+thisMarker,null);
			// Nesto sad ne radi zbog komentarisanja ove linije!!!!!!!!!!!
			//currentDesignator = designatorName.obj = Tab.find(designatorName.getName());
			
			designatorNameStr = designatorName.getName();
			
			if(nestedArr == 0 && !designatorIsRight)leftEnd = "var";

			if(!parentIsMethod(designatorName)&&(loadCondition(designatorName) || 
					designatorName.getParent() instanceof DesignatorArray || (designatorIsRight && !(designatorName.getParent() instanceof DesignatorPoint) && !(designatorName.getParent() instanceof DesignatorArray)))) {
				if(designatorName.getName().contentEquals("this") &&loadCondition(designatorName.getParent())) {

				}else {

					// Ne odnosi se na metodu, vec na polja metode
					switch (currentDesignator.getKind()) {
			    	
				      case Obj.Con:
							Code.load(currentDesignator); 
				        break;
				        
				      case Obj.Var:

							Code.load(currentDesignator);
				        break;
				      case Obj.Fld:
							Code.load(currentDesignator);
				    	  break;
				      case Obj.Elem:
							Code.load(currentDesignator);
				    	  break;
				      default:  
				         //error("Greska: nelegalan operand u Code.load");
				    }
					if(!(partOf(DesignatorActParameters.class, designatorName))&&
							!partOf(StatementPrint.class, designatorName))
					putList(currentDesignator);
					//invokeVirtual = true;
				}
			}else {
				//invokeVirtual = false;
			}
		}

	}
	private boolean arrayEnt = false;
	private boolean desPointBefore = false;
	public void visit(DesignatorPoint designatorPoint) {
		if(prevRemoveCondition(designatorPoint)) {
			List<Obj> objs = prevDesignators.remove(prevDesignators.size()-1);
			//fillPutList(objs);
		}
		//if(currentDesignator!=null)Code.load(currentDesignator);
		Obj previousDesignator = currentDesignator;
		currentDesignator = designatorPoint.obj;
		currentClassDesignator = previousDesignator;
		//if(prevDesignators.size()>0)prevDesignators.get(prevDesignators.size()-1).add(previousDesignator);
		
		//putList(previousDesignator);
		//report_info("Curr des "+currentDesignator,null);
		
		//Load field
		if(!parentIsMethod(designatorPoint)&&(loadCondition(designatorPoint) || designatorPoint.getParent() instanceof DesignatorArray || designatorIsRight)) {
			
			Code.load(currentDesignator);

		}else if(parentIsMethod(designatorPoint)) {
				//Code.put(Code.load);
				//Code.put(0);
			
		}
		if(parentIsMethod(designatorPoint)) invokeVirtual = true;
		if(nestedArr == 0 && !designatorIsRight)leftEnd = "class";
		desPointBefore = true;
	}
	
    // ---------------------- INC & DEC ----------------------
	public void visit(DesignatorIncrement designatorInc) {
		
		if(leftEnd.contentEquals("array_int")) {
			Code.put(Code.dup2);
			Code.put(Code.aload);
		}
		else if(leftEnd.contentEquals("array_not_int")) {
			Code.put(Code.dup2);
			Code.put(Code.baload);
		}else if(leftEnd.contentEquals("class")){
		Code.put(Code.dup);
			Code.load(designatorInc.getDesignator().obj);
		}else {
			Code.load(designatorInc.getDesignator().obj);
		}
		
		Code.loadConst(1);
		Code.put(Code.add);
		
		if(leftEnd.contentEquals("array_int")) {
			Code.put(Code.astore);
		}
		else if(leftEnd.contentEquals("array_not_int")) {
			Code.put(Code.bastore);
		}else {
			Code.store(designatorInc.getDesignator().obj);
		}
		leftEnd = "";
		addTwice = null;
	}
	public void visit(DesignatorDecrement designatorDec) {

		if(leftEnd.contentEquals("array_int")) {
			Code.put(Code.dup2);
			Code.put(Code.aload);
		}
		else if(leftEnd.contentEquals("array_not_int")) {
			Code.put(Code.dup2);
			Code.put(Code.baload);
		}else {
			Code.load(designatorDec.getDesignator().obj);
		}
		
		Code.loadConst(1);
		Code.put(Code.sub);
		
		if(leftEnd.contentEquals("array_int")) {
			Code.put(Code.astore);
		}
		else if(leftEnd.contentEquals("array_not_int")) {
			Code.put(Code.bastore);
		}else {
			Code.store(designatorDec.getDesignator().obj);
		}
		leftEnd = "";
		addTwice = null;
	}

    // ---------------------- OPERATIONS ----------------------
	
	public void visit(MinusEntry minusEntry) {
		minusPresent = true;
	}
	public void visit(TermListEnd termListEnd) {
		if(termListEnd.getParent() instanceof Expression1Hyphen	||
				termListEnd.getParent().getParent() instanceof Expression1Hyphen) {
			Code.put(Code.neg);
		}

		//if(!(termListEnd.getParent() instanceof TermListBody))codePutList.set(codePutList.size()-1, new ArrayList<>());

		minusPresent = false;
	}
	
	
	public void visit(AddOperation addop) {

		List<Put> p = codePutList.get(codePutList.size()-1);
		if(codePutList.size()>1)
		for(Put pp: p) {
			codePutList.get(codePutList.size()-2).add(pp);
		}
		codePutList.set(codePutList.size()-1,new ArrayList<>());
		
	}
	public void visit(SubtractOperation addop) {

		List<Put> p = codePutList.get(codePutList.size()-1);
		if(codePutList.size()>1)
		for(Put pp: p) {
			codePutList.get(codePutList.size()-2).add(pp);
		}
		codePutList.set(codePutList.size()-1,new ArrayList<>());
		
	}
	public void visit(TermListBody term) {
		Addop addop = term.getAddop();
		
		
	if(addop instanceof AddOperation) {
			

		if(!partOf(StatementPrint.class, term))
			putList(Code.add, "code");
			Code.put(Code.add);
		}else if(addop instanceof SubtractOperation) {
			if(!partOf(StatementPrint.class, term))
			putList(Code.sub, "code");
			Code.put(Code.sub);
		}
	
	}

	
	public void visit(TermBody term) {
		Mulop mulop = term.getMulop();
		if(mulop instanceof Multiplication) {
			Code.put(Code.mul);
		}else if(mulop instanceof Division) {
			Code.put(Code.div);
		}else if(mulop instanceof Modulus) {
			Code.put(Code.rem);
		}
	}
	
	public void visit(TermEnd term) {
		
	}
	
	private boolean arrayMethodCall = false;
	
	
	public void visit(OptionalExpression opt) {
		arrayAlloc = true;
	}
	public void visit(NoOptionalExpression opt) {
	}
	public void visit(FactorNew factorNew) {
		if(arrayAlloc) {
			// Expr should be on the stack
			Code.put(Code.newarray);

			if(factorNew.getType().struct.getKind()==Struct.Char) {
				Code.put(0);
			}else { //?? je l i za bool
				Code.put(1);
			}
			
		}else {
			// CLASS

			ClassVarNewVisitor cvs = new ClassVarNewVisitor();

			ClassType cn = null;
			if(factorNew.getType().struct instanceof ClassType)
				cn = (ClassType)factorNew.getType().struct;
			SyntaxNode sn = factorNew;
			while(!(sn instanceof Program)) {
				sn = sn.getParent();
			}
			cvs.targetName = newClassLoad = cn.name;
			//report_info("NN "+newClassLoad,null);
			cvs.sn = sn;
			sn.traverseTopDown(cvs);
			Code.put(Code.new_);
			Code.put(0);
			
			// CHANGE!!!!!!!!!!!!!!
			Code.put(cvs.varSize+4);
			
			
			
			
			Code.put(Code.dup);
		}
		arrayAlloc = false;
	}

	
    // ---------------------- ARRAY ----------------------
	// Start of array
	public void visit(ArrayEntry arrEntry) {
		if(nestedArr == 0)arrayEnt = designatorIsRight;
		designatorIsRight = true;
		nestedArr++;
		

		codePutList.add(new ArrayList<Put>());
		
	}
	// End of array
	public void visit(DesignatorArray designatorArray) {
		
		report_info("CLOSING "+codePutList.size(),null);
		
		
		if(prevRemoveCondition(designatorArray)) {
			List<Obj> objs = prevDesignators.get(prevDesignators.size()-1);
			//fillPutList(objs);
				if(prevDesignators.size()>0) {
					
				}
		}
		if(!parentIsMethod(designatorArray)) {

			
			if(!(designatorArray.getParent() instanceof Designator) && codePutList.size()==1) {
				//codePutList.set(0, new ArrayList<>());
			}
		}
		arrayMethodCall = true;
		
		//prevDesignators.get(prevDesignators.size()-1).add(currentDesignator);
		
		//putList(currentDesignator);
		
		currentDesignator = designatorArray.obj;
		
		String elemType = currentDesignator.getType().getKind() == Struct.Char ? "_not_int" : "_int";
			
		if(--nestedArr == 0) {
			designatorIsRight = arrayEnt;
		}
		if(!parentIsMethod(designatorArray)&&(loadCondition(designatorArray) ||nestedArr>0||(arrayEnt && !(designatorArray.getParent() instanceof DesignatorPoint)))) {
			
			if(elemType.equals("_int")) {
				Code.put(Code.aload);
				putList(Code.aload,"code");
			}else {
				Code.put(Code.baload);
				putList(Code.baload,"code");
			}
		}else {
			if(nestedArr == 0 && !designatorIsRight)leftEnd = "array"+elemType;
		}
		
		
		//Code.put(Code.dup);
		if(codePutList.size()>0 ) {
			List<Put> putL = codePutList.remove(codePutList.size()-1);

			if(designatorArray.getParent() instanceof Designator)
			for(Put p : putL) {

				// Add to previous level
				putList(p);
				
				if(!(designatorArray.getParent().getParent() instanceof FactorMethod ||
				designatorArray.getParent().getParent() instanceof DesignatorFunctionCall)) {
				
					if(p.type.contentEquals("obj")) {
					Code.load(p.obj);
				}else if(p.type.contentEquals("code")){
					Code.put(p.code);
				}else {
					if(p.isPut4) {
						Code.put4(p.val);
					}else {
	
						Code.loadConst(p.val);
					}
				}
				}
			}

			//if(!(designatorArray.getParent() instanceof Designator)&&codePutList.size()==1 ) codePutList.set(0,new ArrayList<>());
		}

	}
	private int ifLevel = 0;
    // ---------------------- IF BODY ----------------------
	
	private String conditionConstruct = "";
	
	// Start
	public void visit(UnmatchedIf ui) {
		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
	public void visit(UnmatchedElse ui) {
		if(isCompleteIfElse(ui)) {
			patchUp("if_end", 0);
			codePutList.set(codePutList.size()-1, new ArrayList<>());
		}
	}
	public void visit(StatementIfElse ui) {
		patchUp("if_end", 0);
		codePutList.set(codePutList.size()-1, new ArrayList<>());

		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
	
	public void visit(IfIdentifier ifId) {
		level++;
		ifLevel++;
		conditionConstruct = "if";
		codePutList.set(codePutList.size()-1, new ArrayList<>());
		codePutList.add(new ArrayList<>());
	}
	
	// End
	public void visit(IfMatched im) {
		// Skip the jmp
		Code.pc += 3;
		patchUp("if", level);
		Code.pc -= 3;
		patches.add(new Patch(Code.pc+1,"if_end", 0));

		Code.putJump(0);
		level--;
		ifLevel--;
		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
	public void visit(IfStatement im) {
		patchUp("if", level);
		level--;
		ifLevel--;
		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
	public void visit(ElseMatched im) {

		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
	public void visit(ElseUnmatched im) {

		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
    // ---------------------- CONDITIONS ----------------------
	
	int op = -1;
	
	List<Patch> patches = new ArrayList<Patch>();
	int level = 0;
	// Relop
	public void visit(ExpressionList expr) {
		if(partOf(TernaryStart.class, expr)) conditionConstruct = "ternary";
		Relop relop = expr.getRelop();
		if(relop instanceof RelopEquals) {
			op = Code.eq;
		}else if(relop instanceof RelopDoesNotEqual) {
			op = Code.ne;
		}else if(relop instanceof RelopGreater) {
			op = Code.gt;
		}else if(relop instanceof RelopGreaterOrEqual) {
			op = Code.ge;
		}else if(relop instanceof RelopLess) {
			op = Code.lt;
		}else if(relop instanceof RelopLessOrEqual) {
			op = Code.le;
		}

		if(conditionConstruct.contentEquals("if")) {
			patches.add(new Patch(Code.pc+1,"or, if", level));
			Code.putFalseJump(op, 0);
		}else if(conditionConstruct.contentEquals("do")) {
			Code.putFalseJump(Code.inverse[op], doReturn.get(doReturn.size()-1));
		}
		
	}

	public void visit(ExpressionListEnd expr) {
		if(partOf(TernaryStart.class, expr)) conditionConstruct = "ternary";
		
		
		if(conditionConstruct.contentEquals("if")) {
			Code.loadConst(0);
			patches.add(new Patch(Code.pc+1,"or, if", level));
			Code.putFalseJump(Code.ne, 0);
		}else if(conditionConstruct.contentEquals("do")) {
			Code.putFalseJump(Code.inverse[op], doReturn.get(doReturn.size()-1));
		}
		op = -1;
		//conditionConstruct = "";
	}
	// AND
	public void visit(ConditionFactList condFactList) {
	}
	
	//OR
	public void visit(ConditionTermList condTermList) {
		
	}
	public void visit(Condition cond) {
		conditionConstruct = "";
		codePutList.set(codePutList.size()-1, new ArrayList<>());
	}
	public void visit(OrOp orOp) {
		patchUp("or", level);
	}
	

	public void visit(AndOp andOp) {}

    // ---------------------- METHODS ----------------------
	
	private String getMethodClass(SyntaxNode sn) {
		while(!(sn instanceof ClassDeclaration) && sn!=null) {
			sn = sn.getParent();
		}
		
		
		if(sn==null) return null;
		ClassDeclaration cd = (ClassDeclaration) sn;
		
		ClassName cn = cd.getClassName();
		
		return cn.getClassName();
	}
	
	public void visit(MethodVoid methodVoid) {

		classVarNames = new ArrayList<>();
		methodAddresses.put(getMethodClass(methodVoid)+"."+methodVoid.getMethName(), Code.pc);
		
		
		
		if ("main".equalsIgnoreCase(methodVoid.getMethName())) {
			
			mainPc = Code.pc;
		}
		//report_info(methodVoid.getMethName(),null);

		//report_info(Code.pc+"",null);
		
		
		
		SyntaxNode methodNode = methodVoid.getParent();
		FormParamCounter fpCnt = new FormParamCounter();
		methodNode.traverseTopDown(fpCnt);

		int fpCount = fpCnt.getCount();
		
		VarCounter varCnt = new VarCounter();
		methodNode.traverseTopDown(varCnt);
		
		int varCount = varCnt.getCount();

		if(getMethodClass(methodVoid)!=null) {
			fpCount++;
		}
		
		methodVoid.obj.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(fpCount);
		Code.put(fpCount+varCount);
		


		if ("main".equalsIgnoreCase(methodVoid.getMethName())) {
			// Virtual table
	
			SyntaxNode sn = methodVoid.getParent();
			
			while(!(sn instanceof Program)) {
				sn = sn.getParent();
			}
			
			
			ClassVisitor cms = new ClassVisitor(this.methodAddresses);
			sn.traverseTopDown(cms);
			
			tvfAddresses = cms.tvfAddresses;
		}

		codePutList.add(new ArrayList<>());
		//Code.loadConst(-2);
	}
	

	public void visit(MethodDeclaration methodDeclaration) {
		patchUp("return",0);
	    Code.put(Code.exit);
	    Code.put(Code.return_);
	    if(codePutList.size()>0)
		codePutList.remove(codePutList.size()-1);
	}
	public void visit(MethodType methodType) {
		classVarNames = new ArrayList<>();
		methodAddresses.put(getMethodClass(methodType)+"."+methodType.getMethName(), Code.pc);
		
		//report_info(methodType.getMethName(),null);

		//report_info(Code.pc+"",null);
		
		
		
		SyntaxNode methodNode = methodType.getParent();
		FormParamCounter fpCnt = new FormParamCounter();
		methodNode.traverseTopDown(fpCnt);

		int fpCount = fpCnt.getCount();
		
		VarCounter varCnt = new VarCounter();
		methodNode.traverseTopDown(varCnt);
		
		int varCount = varCnt.getCount();

		if(getMethodClass(methodType)!=null) {
			fpCount++;
		}
		methodType.obj.setAdr(Code.pc);
		Code.put(Code.enter);
		Code.put(fpCount);
		Code.put(fpCount+varCount);
		//Code.loadConst(-2);
		codePutList.add(new ArrayList<>());
	}
	

	public void visit(StatementPrint stmtPrint) {

		Expr expr = stmtPrint.getExpr();
		Code.put(Code.const_5);
		if(expr.struct.getKind() == Struct.Int) {
			Code.put(Code.print);
		}else {
			Code.put(Code.bprint);
		}
	}
	
	// CHAR ARR
	public void visit(FactorChar factorChar) {
		Code.loadConst(factorChar.getValue());
	}
	
    // ---------------------- METHOD CALL ----------------------
	String invokeVirtualName = null;
	public void visit(DesignatorFunctionCall desFunc) {
		Obj obj=null;
		if(desFunc.getDesignator() instanceof DesignatorName)obj = ((DesignatorName)desFunc.getDesignator()).obj;
		else if(desFunc.getDesignator() instanceof DesignatorPoint)obj = ((DesignatorPoint)desFunc.getDesignator()).obj;
		else if(desFunc.getDesignator() instanceof DesignatorArray)obj = ((DesignatorArray)desFunc.getDesignator()).obj;
		
		int methodAdr = obj.getAdr();


		int offset = methodAdr - Code.pc;
		boolean flag = true;
		if(desFunc.getDesignator() instanceof DesignatorName) {
			DesignatorName dn = (DesignatorName) desFunc.getDesignator();
			if(dn.getName().contentEquals("len")) {
				flag = false;
					Code.put(Code.arraylength);
			}else if(dn.getName().contentEquals("ord")) {

				flag = false;
			}else if(dn.getName().contentEquals("read")) {

				Code.put(Code.read);
				flag = false;
			}
		}
		if(flag) 
		if(!invokeVirtual) {
			report_info("ADRR "+designatorNameStr+" "+methodAdr,null);

			codePutList.add(new ArrayList<>());
			Code.put(Code.call);
			Code.put2(offset);
			codePutList.remove(codePutList.size()-1);
			
		}else {
			//Code.put(Code.dup);
			
			
			Code.put(Code.getfield);
			Code.put2(0);

			putList(Code.getfield, "code");
			putList(0, "code");
			putList(0, "code");
				String name = null;
				if(desFunc.getDesignator() instanceof DesignatorPoint) {
					DesignatorPoint dp = (DesignatorPoint)desFunc.getDesignator();
					 name = dp.getName();
				}
				else if(desFunc.getDesignator() instanceof DesignatorName) {
					DesignatorName dn = (DesignatorName)desFunc.getDesignator();
					 name = dn.getName();
				}
				//report_info("NAME "+name,null);
				invokeVirtualName = name;
				codePutList.add(new ArrayList<>());
				
				Code.put(Code.invokevirtual);
				for(int i=0;i<name.length();i++) {
					Code.put4(name.charAt(i));
				}
				
				Code.put4(-1);
				codePutList.remove(codePutList.size()-1);
			
		}
		
		codePutList.set(codePutList.size()-1,new ArrayList<>());
		
	}
	public void visit(FactorMethod factMeth) {
		thisMarker = false;
		Obj obj = null;
		if(factMeth.getDesignator() instanceof DesignatorName)obj = ((DesignatorName)factMeth.getDesignator()).obj;
		else if(factMeth.getDesignator() instanceof DesignatorPoint)obj = ((DesignatorPoint)factMeth.getDesignator()).obj;
		else if(factMeth.getDesignator() instanceof DesignatorArray)obj = ((DesignatorArray)factMeth.getDesignator()).obj;
		
		currentDesignator = obj;
		
		int methodAdr = obj.getAdr();
		int offset = methodAdr - Code.pc;
		boolean flag = true;
		if(factMeth.getDesignator() instanceof DesignatorName) {
			DesignatorName dn = (DesignatorName) factMeth.getDesignator();
			if(dn.getName().contentEquals("len")) {
				flag = false;
					Code.put(Code.arraylength);
			}else if(dn.getName().contentEquals("ord")) {

				flag = false;
			}else if(dn.getName().contentEquals("read")) {

				Code.put(Code.read);
				flag = false;
			}
		}
		if(flag) {
			if(!invokeVirtual) {
				codePutList.add(new ArrayList<>());
				Code.put(Code.call);
				Code.put2(offset);
				codePutList.remove(codePutList.size()-1);
			}else {
				//Code.put(Code.dup);
				Code.put(Code.getfield);
				Code.put2(0);
				
				putList(Code.getfield, "code");
				putList(0, "code");
				putList(0, "code");

				putList(Code.invokevirtual,"code");
				if(factMeth.getDesignator() instanceof DesignatorPoint) {
					DesignatorPoint dp = (DesignatorPoint)factMeth.getDesignator();
				
					String name = dp.getName();
					//report_info("NAME "+name,null);
					invokeVirtualName = name;
					putListName(name);
					
					codePutList.add(new ArrayList<>());
					
					Code.put(Code.invokevirtual);
					for(int i=0;i<name.length();i++) {
						Code.put4(name.charAt(i));
					}
					
					Code.put4(-1);
					codePutList.remove(codePutList.size()-1);
				}else {
					DesignatorName dp = (DesignatorName)factMeth.getDesignator();
					
					String name = dp.getName();
					//report_info("NAME "+name,null);
					invokeVirtualName = name;
					putListName(name);

					codePutList.add(new ArrayList<>());
					
					Code.put(Code.invokevirtual);
					for(int i=0;i<name.length();i++) {
						Code.put4(name.charAt(i));
					}
					
					Code.put4(-1);
					codePutList.remove(codePutList.size()-1);
				}
			}
		}
		report_info("SIZE "+designatorNameStr+" "+codePutList.get(codePutList.size()-1).size(),null);
		//codePutList.set(codePutList.size()-1,new ArrayList<>());
		
	}
	
	
	
    // ---------------------- DO WHILE ----------------------
	
	public void visit(DoIdentifier doIdent) {
		level++;
		doReturn.add(Code.pc);
	}
	public void visit(WhileIdentifier whileIdent) {
		conditionConstruct = "do";
		patchUp("continue", level);
	}
	public void visit(StatementDoWhile doWhile) {
		doReturn.remove(doReturn.size()-1);
		//?
		//report_info("LEVEL "+(level),null);
		patchUp("break", level--);
	}
	

    // ---------------------- SWITCH ----------------------
	public void visit(SwitchIdentifier swId) {
		level++;
	}
	public void visit(StatementSwitch stmtSw) {
		patchUp("switch",level);
		patchUp("switch_case_end", level);
		patchUp("break", level);
		// One element will be left on the expression stack
		Code.put(Code.pop);
		
		level--;
		
	}
	public void visit(SwitchExpression switchExpr) {
	}
	public void visit(SwitchElementTrue switchCase) {
		patches.add(new Patch(Code.pc+1,"switch_case_end", level));
		Code.putJump(0);
	}
	
	public void visit(SwitchElementStart swStart) {
		patchUp("switch", level);
		Code.put(Code.dup);
		Code.loadConst(swStart.getNumber());
		patches.add(new Patch(Code.pc+1,"switch", level));
		Code.putFalseJump(Code.eq,0);
		patchUp("switch_case_end", level);
	}

    // ---------------------- BREAK & CONTINUE ----------------------
	public void visit(StatementBreak stmtBreak) {

		//report_info("LEVEL PUT "+(level),null);
		patches.add(new Patch(Code.pc+1,"break", level-ifLevel));
		Code.putJump(0);
	}

	public void visit(StatementContinue stmtContinue) {

		patches.add(new Patch(Code.pc+1,"continue", level-1));
		Code.putJump(0);
	}
 
    // ---------------------- TERNARY ----------------------
	public void visit(TernaryStart tern) {
		level++;
		conditionConstruct = "ternary";
		
		if(op == -1) {
			Code.loadConst(0);
			patches.add(new Patch(Code.pc+1,"ternary", level));
			Code.putFalseJump(Code.ne, 0);
		}else {
			patches.add(new Patch(Code.pc+1,"ternary", level));
			Code.putFalseJump(op, 0);
		}
	}
	public void visit(ExpressionTern tern) {
		
		patchUp("ternary", level);
		level--;
	}
	public void visit(Expression tern) {
		
	}
	public void visit(RightExpr rightExpr) {
	}
	
	public void visit(LeftExpr rightExpr) {
		Code.pc += 3;
		patchUp("ternary", level);
		Code.pc -= 3;
		patches.add(new Patch(Code.pc+1,"ternary", level));
		Code.putJump(0);
	}

    // ---------------------- INNER CLASS ----------------------
    boolean isOfDP(SyntaxNode dap) {
    	if(dap.getParent() instanceof FactorMethod) {
    		FactorMethod fm = (FactorMethod) dap.getParent();
    		if(fm.getDesignator() instanceof DesignatorPoint) {
    			return true;
    		}
    	}else if(dap.getParent() instanceof DesignatorFunctionCall) {
    		return true;
    	}
    	return false;
    }
	public void visit(DesignatorActParameters dap) {
		List<Put> addList = new ArrayList<Put>();
		//report_info("CONSTNUM "+constNum,null);
		
		if(codePutList.size()>0 && isOfDP(dap)) {
			List<Put> putL = codePutList.get(codePutList.size()-1);
			
			
			for(Put p : putL) {
				// Add to previous level
				addList.add(p);

				
				if(p.type.contentEquals("obj")) {
					Code.load(p.obj);
				}else if(p.type.contentEquals("code")){
					Code.put(p.code);
				}else if(p.type.contentEquals("name")){
					String name = p.name;
					for(int i=0;i<name.length();i++) {
						Code.put4(name.charAt(i));
					}
					
					Code.put4(-1);
				}else {
					Code.loadConst(p.val);
					
				}
			}for(Put p: paramPutList) {
				
				putList(p);
			}
			if(invokeVirtualName!=null) {
				/*putList(Code.invokevirtual,"code");
				report_info("PUT NAME "+invokeVirtualName,null);
				putListName(invokeVirtualName);
				invokeVirtualName = null;*/
			}
			for(Put p:addList) {
				putList(p);
			}
			
			if(!(dap.getParent() instanceof Designator)&&codePutList.size()==1) codePutList.set(0,new ArrayList<>());
		}
		//List<Obj> prevDesignatorList = prevDesignators.remove(prevDesignators.size()-1);

	
		paramPutList = new ArrayList<>();
		if(invokeVirtual|| partOf(ClassDeclaration.class, dap)) {
			if(thisMarker) {

				//Code.put(Code.load);
				//Code.put(0);

			}

			/*if(!arrayMethodCall)
				for (Obj obj : prevDesignatorList) {

					Code.load(obj);
				}*/
			
			
		}
	}
	public void visit(NoDesignatorActParameters dap) {
		List<Put> addList = new ArrayList<Put>();
		if(codePutList.size()>0 && isOfDP(dap)) {
			List<Put> putL = codePutList.get(codePutList.size()-1);
			
			//if(((FactorMethod)dap.getParent()).getDesignator() instanceof DesignatorArray)codePutList.remove(codePutList.size()-1);
			
			report_info("METHTHT ",null);
			for(Put p : putL) {
				// Add to previous level
				addList.add(p);
				
				if(p.type.contentEquals("obj")) {
					Code.load(p.obj);
				}else if(p.type.contentEquals("code")){
					Code.put(p.code);
				}else if(p.type.contentEquals("name")){
					String name = p.name;
					for(int i=0;i<name.length();i++) {
						Code.put4(name.charAt(i));
					}
					
					Code.put4(-1);
				}else {
						Code.loadConst(p.val);
					
				}
			}
			for(Put p: paramPutList) {
			
				putList(p);
			}
			if(invokeVirtualName!=null) {
				/*putList(Code.invokevirtual,"code");
				report_info("PUT NAME "+invokeVirtualName,null);
				putListName(invokeVirtualName);
				invokeVirtualName = null;*/
			}
			for(Put p:addList) {
				putList(p);
			}
			
			
			
			if(!(dap.getParent() instanceof Designator) && codePutList.size()==1)codePutList.set(0,new ArrayList<>());
		}
		//List<Obj> prevDesignatorList = prevDesignators.remove(prevDesignators.size()-1);
	
		paramPutList = new ArrayList<>();
		if(invokeVirtual|| partOf(ClassDeclaration.class, dap)) {
			if(thisMarker) {

				//Code.put(Code.load);
				//Code.put(0);
				
			}
			/*	if(!arrayMethodCall)
				for (Obj obj : prevDesignatorList) {

					Code.load(obj);
					
				}*/
				
		} 
	}
	public void visit(ParameterEntry parEntry) {
		//codePutList.add(new ArrayList<Put>());
	}
	public void visit(ActParameters ap) {

		/*codePutList.remove(codePutList.size()-1);
		if(ap.getParent() instanceof ActParameters)
		codePutList.add(new ArrayList<Put>());*/
	}
	public void visit(ActParametersEnd ap) {
		//codePutList.remove(codePutList.size()-1);
	}
	HashMap<String,Integer> classSizes = new HashMap<String,Integer>();
	String classSizeName = null;
	public void visit(ClassName cn) {
		classSizeName = cn.getClassName();
		classSizes.put(classSizeName, 0);
		
		varSize = 0;
	}
	
	public void visit(ClassExtendsTrue cc) {

		ClassType cn = null;
		if(cc.getType().struct instanceof ClassType)
			cn = (ClassType)cc.getType().struct;
		classSizes.put(classSizeName, classSizes.get(classSizeName)+classSizes.get(cn.name));
	}
	public void visit(ClassDeclaration cn) {
		varSize = 0;
	}
	public void visit(ClassVariable cv) {
		classSizes.put(classSizeName, classSizes.get(classSizeName)+4);
	
		varSize+=4;
	}

	public void visit(ClassVariableArray cv) {
		classSizes.put(classSizeName, classSizes.get(classSizeName)+4);
		varSize+=4;
	}
	
	
	public void visit(FormalParameterDeclaration fpd) {

		classVarNames.add(fpd.getParam());
	}
	
	public void visit(FormParams fp) {

	}
	public void visit(NoFormParam nfp) {

	}
	public void visit(Variable v) {
	if(partOf(MethodVarDeclarationList.class, v)) {	
		if(classVarNames != null)classVarNames.add(v.getVarName());
	
		}
	}
	public void visit(VariableArray va) {
	if(partOf(MethodVarDeclarationList.class, va)) {	if(classVarNames != null)classVarNames.add(va.getVarName());
		
		}
	}
	
	public void visit(StatementReturnExpr sre) {
		patches.add(new Patch(Code.pc+1,"return", 0));
		Code.putJump(0);
	}
	// Mislim da continue vraca na do, a ne na while
	// DataSize
	// print(predmeti[0].r);
	// Ucitavanje parametara fje
	// char
	// Pop za metode
	//TRAP
}