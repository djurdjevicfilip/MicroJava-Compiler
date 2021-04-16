package rs.ac.bg.etf.pp1;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.MethodVisitor.ClassMethodVisitor;
import rs.ac.bg.etf.pp1.MethodVisitor.ClassVarNewVisitor;
import rs.ac.bg.etf.pp1.MethodVisitor.ClassVarVisitor;
import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;


public class MethodVisitor extends VisitorAdaptor {
	Logger log = Logger.getLogger(getClass());

	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message); 
		int line = (info == null) ? 0: info.getLine();
		if (line != 0)
			msg.append (" na liniji ").append(line);
		log.info(msg.toString());
	}
	public int classVars = 0;
	// ClassVars u zavisnosti od toga da li je izvedena klasa ???
	private void addToVirtualTable(String name, int address, int cl) {
		
	}
	public static class ClassMethodVisitor extends MethodVisitor {
		public HashMap<String, Integer> methodAddresses = new HashMap<String,Integer>();
		
		public ClassMethodVisitor(HashMap<String, Integer> methodAddresses ) {
			this.methodAddresses = methodAddresses;
		}
		private String getMethodClass(SyntaxNode sn) {
			while(!(sn instanceof ClassDeclaration)) sn = sn.getParent();
			
			ClassDeclaration cd = (ClassDeclaration) sn;
			
			ClassName cn = cd.getClassName();
			
			return cn.getClassName();
		}
		
		@Override
		public void visit(MethodVoid mv) {
			String name = mv.getMethName();
			for (int i = 0; i < name.length(); i++) {
				Code.loadConst(name.charAt(i));
				Code.put(Code.putstatic);
				Code.put(0);
				Code.put(classVars++);
			}
			
			Code.loadConst(-1);
			Code.put(Code.putstatic);
			Code.put(0);
			Code.put(classVars++);

			Code.loadConst(methodAddresses.get(getMethodClass(mv)+"."+name));
			Code.put(Code.putstatic);
			Code.put(0);
			Code.put(classVars++);
		}	
		@Override
		public void visit(MethodType mv) {
			String name = mv.getMethName();
			for (int i = 0; i < name.length(); i++) {
				Code.loadConst(name.charAt(i));
				Code.put(Code.putstatic);
				Code.put(0);
				Code.put(classVars++);
			}
			
			Code.loadConst(-1);
			Code.put(Code.putstatic);
			Code.put(0);
			Code.put(classVars++);

			Code.loadConst(methodAddresses.get(getMethodClass(mv)+"."+name));
			Code.put(Code.putstatic);
			Code.put(0);
			Code.put(classVars++);
		}
	}
	public static class ClassVisitor extends MethodVisitor{

		
		
		
		public HashMap<String, Integer> tvfAddresses = new HashMap<String,Integer>();
		public HashMap<String, Integer> methodAddresses = new HashMap<String,Integer>();
		
		public ClassVisitor(HashMap<String, Integer> methodAddresses ) {
			this.methodAddresses = methodAddresses;
		}
		
		private void openVirtualTable(String className) {
			tvfAddresses.put(className, classVars);
			//classVars = 0;
		}
		private void closeVirtualTable() {

			Code.loadConst(-2);
			Code.put(Code.putstatic);
			Code.put(0);
			Code.put(classVars++);
			//classVars = 0;
		}
	    // Start of class
	    public void visit(ClassName className) {
	    	openVirtualTable(className.getClassName());

			ClassVarVisitor cvs = new ClassVarVisitor();

			className.getParent().traverseTopDown(cvs);
			
			ClassMethodVisitor cms = new ClassMethodVisitor(this.methodAddresses);
		//cvs.classVars;
			
			cms.classVars = classVars;
			
			className.getParent().traverseTopDown(cms);

	    	classVars = cms.classVars;
	    	
	    	
	    }
	    public void visit(ClassExtendsTrue classExtends) {
	    	
	    	ClassType extendedType = null;
	    	if(classExtends.getType().struct instanceof ClassType) {
	    		extendedType = (ClassType) classExtends.getType().struct;
	    	}
	    	
	    	String extendedClassName = extendedType.name;
	    	
	    	ClassDeclaration cd= (ClassDeclaration) classExtends.getParent();
	    	ClassName clName = cd.getClassName();
	    	String className = clName.getClassName();
	    	HashMap<String, Integer> tmpHash = new HashMap<>();
	    	for (Map.Entry<String,Integer> entry : methodAddresses.entrySet()) {
	    		String methAdrStr = entry.getKey();
	    		int methAdr = entry.getValue();
	    		
	    		if(methAdrStr.startsWith(extendedClassName)) {
	    		
				String methName = methAdrStr.subSequence(extendedClassName.length()+1, methAdrStr.length()).toString();
				
					if(!methodAddresses.containsKey(className+"."+methName)) {
							for (int i = 0; i < methName.length(); i++) {
								Code.loadConst(methName.charAt(i));
								Code.put(Code.putstatic);
								
								Code.put2(classVars++);
							}
							
							Code.loadConst(-1);
							Code.put(Code.putstatic);
							Code.put2(classVars++);
							Code.loadConst(methAdr);
							Code.put(Code.putstatic);
							tmpHash.put(className+"."+methName, methAdr);
							Code.put2(classVars++);
						}
					}
	    		
	    	}
    		methodAddresses.putAll(tmpHash);
	    	closeVirtualTable();
	    }
	    public void visit(NoClassExtends nce) {

	    	closeVirtualTable();
	    }
	    // End of class
	    public void visit(ClassDeclaration classDeclaration) {
	    	
	    }
	   
	}
	public static class ClassVarVisitor extends MethodVisitor {
		
	 public void visit(ClassVariable var){
	    	classVars++;
		}
	    
	    public void visit(ClassVariableArray var){
	    	classVars++;
	    }
	}
	public static class ClassVarNewVisitor extends MethodVisitor {
		public String targetName;
		public SyntaxNode sn;
		public int varSize;
		public boolean count = false;
		public void visit(ClassName cname) {
			if(cname.getClassName().contentEquals(targetName)) {
				count = true;
			}
			
		}
		public void visit(ClassExtendsTrue cet) {
			if(count) {
				ClassVarNewVisitor cvs = new ClassVarNewVisitor();

				ClassType cn = null;
				if(cet.getType().struct instanceof ClassType)
					cn = (ClassType)cet.getType().struct;
				cvs.targetName = cn.name;
				report_info("NNANA "+cn.name,null);
				SyntaxNode snn = cet;
				while(!(snn instanceof Program)) {
					snn = snn.getParent();
				}
				//cvs.sn = sn;

				snn.traverseTopDown(cvs);
				varSize+=cvs.varSize;
			}
		}
		
		
		public void visit(ClassDeclaration cdecl) {
			count = false;
		}
		
		 public void visit(ClassVariable var){
			 if(count)varSize+=4;
			}
		    
		    public void visit(ClassVariableArray var){
		     if(count)varSize+=4;
		    }
		}
}