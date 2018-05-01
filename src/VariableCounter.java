public class VariableCounter {
	private final int DECAY_FACTOR = 4;
	
	private int var;
	private float positive;
	private float negative;
	private float total;
	
	VariableCounter (int variable) {
		var = variable;
	}
	
	public int get() {
		return var;
	}
	
	public void increasePos() {
		positive++;
	}
	
	public void increaseNeg() {
		negative++;
	}
	
	public float getTotal() {
		return positive+negative;
	}
	
	public boolean isPositiveHigher() {
		return positive > negative;
	}
	
	public boolean isValueSame(){
		return positive == negative;
	}
	
	public void decay() {
		if (positive > 0) {
			positive /= DECAY_FACTOR;
		}
		if (negative > 0) {
			negative /= DECAY_FACTOR;
		}
	}
}
