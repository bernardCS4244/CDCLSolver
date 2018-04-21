import java.util.ArrayList;
import java.util.List;

public class Clause {
	private List<Literal> disjunctionOfLiterals;
	
	public Clause() {
		disjunctionOfLiterals = new ArrayList<>();
	}
	
	public void add(Literal newLiteral) {
		disjunctionOfLiterals.add(newLiteral);
	}
	
	public List<Literal> getDisjunctiveClause() {
		return disjunctionOfLiterals;
	}
	
	public boolean hasLiteral(int literalNum) {
		for (Literal literal : disjunctionOfLiterals) {
			if (literalNum == literal.get()) {
				return true;
			}
		}
		return false;
	}
}
