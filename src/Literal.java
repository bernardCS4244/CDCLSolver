
public class Literal {
	final int literal;
	private boolean value;
	
	public Literal(int literal, boolean value) {
		this.literal = literal;
		this.value = value;
	}
	
	public int get() {
		return literal;
	}
	
	public boolean getValue() {
		return value;
	}
	
	public void setValue(boolean newValue) {
		value = newValue;
	}
	
	@Override
	public boolean equals(Object o) {
		Literal lit = (Literal) o;
		return literal == lit.get() && value == lit.getValue();
	}
	
}
