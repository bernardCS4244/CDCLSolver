/**
 * Class to keep track of details edges in the implication graph 
 * 
 */
public class ImplicationDetails {

	private int literalImplied;
	private int clauseUsed;
	
	protected ImplicationDetails(int literalImplied, int clauseUsed) {
		this.literalImplied = literalImplied;
		this.clauseUsed = clauseUsed;
	}
	
	public int getLiteralImplied() {
		return literalImplied;
	}
	
	public int getClauseUsed() {
		return clauseUsed;
	}
}
