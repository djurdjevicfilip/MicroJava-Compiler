package rs.ac.bg.etf.pp1;

import rs.etf.pp1.symboltable.concepts.Struct;

public class ClassType extends Struct{

	public String name = "";
	public ClassType(int kind, String name) {
		super(kind);
		this.name= name;
	}
	
}
