import java.util.List;

public class ConflictClause extends Clause {
	private long timeAdded;
	
	ConflictClause(Clause clause, long timeAdded) {
		super();
		for (Literal literal : clause.getDisjunctiveClause()) {
			super.add(literal);
		}
		this.timeAdded = timeAdded;
	}
	
	public long getTimeAdded() {
		return timeAdded;
	}
}
