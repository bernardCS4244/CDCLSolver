import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Utils {

	public static boolean formulaSatisfied(int numClauses, List<Clause> clauses, Map<Integer, Literal> solution) {
		List<Literal> literals;
		int satisfiedCounter = 0;
		for (int i = 0; i < numClauses; i++) {
			literals = clauses.get(i).getDisjunctiveClause();
			for (Literal literal : literals) {
				Literal literalAssigned = solution.get(literal.get());
				if (literalAssigned != null && (literalAssigned.getValue() == literal.getValue())) {
					satisfiedCounter++;
					break;
				}
			}
		}

		if (satisfiedCounter == numClauses) {
			return true;
		}
		return false;
	}

	public static void printSolution(Action type, int numLiterals, HashMap<Integer, Literal> solution) {
		Literal literal = null;
		for (int i = 1; i <= numLiterals; i++) {
			literal = solution.get(i);
			if (literal == null && type == Action.SAT) {
				System.out.print(i + " ");
			} else if (literal == null && type == Action.UNSAT) {
				System.out.print("* ");
			} else {
				if (literal.getValue()) {
					System.out.print(literal.get() + " ");
				} else {
					System.out.print(literal.get() * -1 + " ");
				}
			}
		}
	}

	public static Clause performResolution(Clause currClause, Clause incomingClause) {
		if (currClause == null) {
			return incomingClause;
		}

		List<Literal> current = currClause.getDisjunctiveClause();
		List<Literal> incoming = incomingClause.getDisjunctiveClause();
		ArrayList<Integer> removeFromIncoming = new ArrayList<>(incoming.size());
		Clause resolutionClause = new Clause();

		boolean literalPresentInBoth;
		for (int i = 0; i < current.size(); i++) {
			literalPresentInBoth = false;
			for (int j = 0; j < incoming.size(); j++) {
				if (current.get(i).get() == incoming.get(j).get()) {
					removeFromIncoming.add(incoming.get(j).get());
					if (current.get(i).getValue() == !incoming.get(j).getValue()) {
						literalPresentInBoth = true;
					}
				}
			}
			if (!literalPresentInBoth) {
				resolutionClause.add(current.get(i));
			}
		}
		for (Literal remainingLiteral : incoming) {
			if (!removeFromIncoming.contains(remainingLiteral.get())) {
				resolutionClause.add(remainingLiteral);
			}
		}

		return resolutionClause;
	}

	public static boolean hasUip(Clause clause, int literalTracker[]) {
		List<Literal> literals = clause.getDisjunctiveClause();
		int count;
		for (int i = 0; i < literals.size(); i++) {
			count = 0;
			for (int j = i + 1; j < literals.size(); j++) {
				count = literalTracker[literals.get(j).get()] < literalTracker[literals.get(i).get()] ? ++count : count;
			}

			for (int k = i - 1; k > -1; k--) {
				count = literalTracker[literals.get(k).get()] < literalTracker[literals.get(i).get()] ? ++count : count;
			}

			if (count == literals.size() - 1) {
				return true;
			}
		}
		return false;
	}

	public static Literal findUnitLiteral(List<Literal> clause, int[] literalTracker,
			HashMap<Integer, Literal> solution) {
		// return null if not unit clause else, returns the only unassigned
		// literal
		int numAssigned = 0;
		Literal unassigned = null;
		if (clause.size() == 1) {
			return clause.get(0);
		} else {
			for (Literal literal : clause) {
				// if already assigned
				if (literalTracker[literal.get()] != -1) {
					numAssigned++;
					// else not assigned, check if there is only one literal
					// unassigned left the whole value of clause if false
				} else {
					unassigned = literal;
				}

				if ((clause.size() - numAssigned == 1) && !isClauseTrue(clause, literalTracker, solution)
						&& unassigned != null) {
					return unassigned;
				}
			}
		}
		return null;
	}

	public static boolean isClauseTrue(List<Literal> clause, int[] literalTracker, HashMap<Integer, Literal> solution) {
		boolean clauseValue = false;
		for (Literal literal : clause) {
			if (literalTracker[literal.get()] != -1) {
				clauseValue = (solution.get(literal.get()).getValue() == literal.getValue()) || clauseValue;
			}
		}
		return clauseValue;
	}
}