/**
 * Class to keep track of details edges in the implication graph
 * 
 */
public class ImplicationDetails {

	private int literalImplied;
	private int clauseUsed;
	private long timeImplied;

	protected ImplicationDetails(int literalImplied, int clauseUsed, long time) {
		this.literalImplied = literalImplied;
		this.clauseUsed = clauseUsed;
		timeImplied = time;
	}

	public int getLiteralImplied() {
		return literalImplied;
	}

	public int getClauseUsed() {
		return clauseUsed;
	}
	
	public long getTimeImplied() {
		return timeImplied;
	}
}
