import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Random;

public class CDCLSolver {
	final int numLiterals;
	final int numOriginalClauses;
	final List<Clause> clausesMasterList;

	int decisionLevel;
	int[] literalTracker;
	boolean[] visited;
	int lastAssignedLiteral;
	int lastClauseUsed; 												// keep track of the last clause used just before a conflict

	HashMap<Integer, Literal> solution; 								// literals with their assigned values
	HashMap<Integer, Boolean> decisionTracker; 							// tracks which literal is assigned by decision
	HashMap<Integer, List<Boolean>> decisionPool; 						// tracks what value have not been assigned by decision for each literal
	HashMap<Integer, Literal> literalPool; 								// so that we don't have to keep creating new literal objects
	HashMap<Integer, Literal> solutionPool;
	HashMap<Integer, List<Integer>> implicationGraph; 					// graph to track which literal is implied from which literal
	HashMap<Integer, List<ImplicationDetails>> reverseImplicationGraph; // implication graph with reversed edges
	private Action result;

	public CDCLSolver(int numLiterals, List<Clause> clauses) {
		this.numLiterals = numLiterals;
		this.numOriginalClauses = clauses.size();
		this.clausesMasterList = clauses;

		System.out.println(numLiterals);
		System.out.println(numOriginalClauses);

		/*********************************************************
		 * Initialization
		 *********************************************************/
		decisionLevel = 0;
		lastAssignedLiteral = 0;
		solution = new HashMap<Integer, Literal>();
		literalPool = new HashMap<Integer, Literal>();
		solutionPool = new HashMap<Integer, Literal>();
		decisionPool = new HashMap<Integer, List<Boolean>>();
		decisionTracker = new HashMap<Integer, Boolean>();
		implicationGraph = new HashMap<Integer, List<Integer>>();
		reverseImplicationGraph = new HashMap<Integer, List<ImplicationDetails>>();
		/**********************************************************/

		// keep track of which literals have been assigned. int indicated the
		// decision level when literal is assigned
		literalTracker = new int[numLiterals + 1];

		// set all literals to unassigned in tracker
		for (int i = 0; i <= numLiterals; i++) {
			// set all literal to unassigned
			literalTracker[i] = -1;

			// populate the literal pool and solution pool
			literalPool.put(i, new Literal(i, true));

			solutionPool.put(i, new Literal(i, true));

			// initialize decision tracker to all literal as not decided
			decisionTracker.put(i, false);

			// initialize implication graphs
			implicationGraph.put(i, new ArrayList<>());
			reverseImplicationGraph.put(i, new ArrayList<>());

			// initialize all literals in the decision pool with 2 values
			ArrayList<Boolean> decisionValues = new ArrayList<>();
			decisionValues.add(true);
			decisionValues.add(false);
			decisionPool.put(i, decisionValues);
		}
	}

	public Action solve() {
		long timeStart = System.currentTimeMillis();
		result = Action.NONE;
		while (!Utils.formulaSatisfied(numOriginalClauses, clausesMasterList, solution)) {
			if (result == Action.UNSAT) {
				long timeEnd = System.currentTimeMillis();
				System.out.println("Time taken: " + (timeEnd - timeStart) + "ms");
				return result;
			}

			if (solution.size() == numLiterals) {
				result = unitPropagation();
				if (hasConflict()) {
					result = diagnose();
				}

				if (result == Action.NONE) {
					return Action.SAT;
				}
			}

			// check for unit clause
			if (clausesMasterList.size() == 105) {
				clausesMasterList.size();
			}
			result = unitPropagation();
			switch (result) {
			case NONE:
				// decide what value to assign to what variable
				result = decide();
				break;
			case UNIT_PROPAGATION:
				if (hasConflict()) {
					result = diagnose();
				}
				break;
			}
		}
		long timeEnd = System.currentTimeMillis();
		System.out.println("Time taken: " + (timeEnd - timeStart) + "ms");
		return Action.SAT;
	}

	// find unit clause or perform unit propagation
	// return: 1 if unit unit propagation done;
	// return: -1 for conflict
	// return: 0 if no unit clause found or there no unit propagation done
	private Action unitPropagation() {
		Action result = Action.NONE;
		lastClauseUsed = -1;
		for (Clause clause : clausesMasterList) {
			final List<Literal> literals = clause.getDisjunctiveClause();
			++lastClauseUsed;
			result = handleUnitClause(Utils.findUnitLiteral(literals, literalTracker, solution));
			if (result != Action.NONE) {
				return result;
			}
		}
		// no unit propagation done
		return result;
	}


	private Action decide() {
		//return randomVariableSelection();
		return naiveVariableSelection();
	}

	// conflict analysis and back tracking
	private Action diagnose() {
		Clause learntClause = learnNewClauseWithUip();
		//Clause learntClause = learnNewClause();
		if (learntClause.getDisjunctiveClause().size() == 0) {
			return Action.UNSAT;
		}

		backTrack(learntClause);
		return Action.NONE;
	}

	// return 0 nothing is done
	// return 1 unit literal is added to solution
	// return -1 if there is a conflict
	private Action handleUnitClause(Literal unitLit) {
		if (unitLit == null) {
			return Action.NONE;
		}
		// if the only literal in unassigned
		if (literalTracker[unitLit.get()] == -1) {
			// if literal is negative, the assigned value must be false. same
			// for positive literal
			addToSolution(unitLit, Action.UNIT_PROPAGATION);
			return Action.UNIT_PROPAGATION;

			// if the assigned value in solution is different from that in the
			// clause = conflict
		} else if ((unitLit.getValue() != solution.get(unitLit.get()).getValue())) {
			// conflict!
			return Action.CONFLICT;
		}
		return Action.NONE;
	}
	
	// decide what value to assign to remaining unassigned literals
	//currently a naive version of choosing the first unassigned literal
	private Action naiveVariableSelection() {
		Literal currLit;
		List<Boolean> decisionValues;
		for (int i = 1; i <= numLiterals; i++) {
			// checks if literal is not assigned and there are still values not
			// used in decision making for that literal
			decisionValues = decisionPool.get(i);
			if (literalTracker[i] == -1 && !decisionValues.isEmpty()) {
				currLit = literalPool.get(i);
				// default value of new literal is assigned true
				addToSolution(currLit, Action.DECIDE);
				decisionTracker.put(currLit.get(), true);
				return Action.NONE;
			}
		}
		// all values have been used but still no satisfiable result found
		System.out.println("no more decision values");
		return Action.UNSAT;
	}
	
	//randomly chooses an unassigned literal and value
	private Action randomVariableSelection() {
		int nextLitNum = -1; 
		while (nextLitNum == -1) {
			nextLitNum = new Random().nextInt(numLiterals+1);
			if (nextLitNum == 0 || literalTracker[nextLitNum] != -1) {
				nextLitNum = -1;
			}
		}
		Literal nextLiteral = literalPool.get(nextLitNum);
		if (new Random().nextBoolean()) {
			nextLiteral.setValue(true);
		} else {
			nextLiteral.setValue(false);
		}
		
		addToSolution(nextLiteral, Action.DECIDE);
		decisionTracker.put(nextLiteral.get(), nextLiteral.getValue());
		
		return Action.NONE;
	}

	private void addToSolution(Literal literal, Action actionDone) {
		Literal literalToAdd = solutionPool.get(literal.get());
		if (literal.getValue()) {
			literalToAdd.setValue(true);
		} else {
			literalToAdd.setValue(false);
		}

		solution.put(literalToAdd.get(), literalToAdd);
		lastAssignedLiteral = literal.get();
		if (actionDone == Action.DECIDE) {
			literalTracker[literal.get()] = ++decisionLevel;
		} else if (actionDone == Action.UNIT_PROPAGATION) {
			literalTracker[literal.get()] = decisionLevel;
			addToImplicationGraph(lastClauseUsed, Action.UNIT_PROPAGATION);
		}
	}

	private boolean hasConflict() {
		for (int i = 0; i < clausesMasterList.size(); i++) {
			// only check for conflict in clauses with all literals assigned
			List<Literal> listOfLit = clausesMasterList.get(i).getDisjunctiveClause();
			int numLit = listOfLit.size();
			for (Literal literal : listOfLit) {
				if (literalTracker[literal.get()] != -1) {
					numLit--;
				}
			}
			if (numLit == 0 && !Utils.isClauseTrue(listOfLit, literalTracker, solution)) {
				addToImplicationGraph(i, Action.CONFLICT);
				return true;
			}

		}
		return false;
	}
	
	//learn clause when the conflict clause has a UIP
	private Clause learnNewClauseWithUip() {
		Clause newClause = new Clause();
		boolean[] isClauseChecked = new boolean[clausesMasterList.size()];

		List<ImplicationDetails> outgoingEdges = retrieveOutgoingEdges(0);
		if (outgoingEdges.size() <= 1) {
			return newClause;
		}
		
		for (ImplicationDetails details : outgoingEdges) {
			int clauseUsed = details.getClauseUsed();
			if (!isClauseChecked[clauseUsed]) {
				isClauseChecked[clauseUsed] = true;
				newClause = Utils.performResolution(newClause, clausesMasterList.get(clauseUsed));
			}
			if (Utils.hasUip(newClause, literalTracker)) {
				if (newClause.getDisjunctiveClause().size() > 0) {
					clausesMasterList.add(newClause);
				}
				return newClause;
			}
		}
		
		//cannot find any UIP
		ArrayList<Literal> toRemoveFromNewClause = new ArrayList<>();
		for (Literal literal : newClause.getDisjunctiveClause()) {
			if (!decisionTracker.get(literal.get())) {
				toRemoveFromNewClause.add(literal);
			}
		}
		newClause.getDisjunctiveClause().removeAll(toRemoveFromNewClause);
		if (newClause.getDisjunctiveClause().size() > 0) {
			clausesMasterList.add(newClause);
		}

		return newClause;
	}

	private List<ImplicationDetails> retrieveOutgoingEdges(int from) {
		List<ImplicationDetails> outgoingEdges = new ArrayList<>();
		Queue<Integer> queue = new LinkedList<>();
		boolean[] visited = new boolean[numLiterals + 1];
		queue.add(from);
		List<ImplicationDetails> currentEdges = null;
		while (!queue.isEmpty()) {
			currentEdges = reverseImplicationGraph.get(queue.remove());
			for (ImplicationDetails edge : currentEdges) {
				if (!visited[edge.getLiteralImplied()] && literalTracker[edge.getLiteralImplied()] >= decisionLevel) {
					queue.add(edge.getLiteralImplied());
					visited[edge.getLiteralImplied()] = true;
				}
			}
			outgoingEdges.addAll(currentEdges);
		}
		return outgoingEdges;
	}

	private Clause learnNewClause() {
		Clause newClause = new Clause();
		Literal literal;

		// iterate through literals assigned via decision and has a path to the
		// conflict
		for (int i = 1; i <= numLiterals; i++) {
			visited = new boolean[numLiterals + 1];
			if (decisionTracker.get(i) && hasPathToConflict(i, visited)) {
				literal = solution.get(i);

				// //remove truth value from decision pool
				// if (!decisionPool.get(i).isEmpty()) {
				// for(int j=0; j<decisionPool.get(i).size(); j++) {
				// if (decisionPool.get(i).get(j) == literal.getValue()) {
				// decisionPool.get(i).remove(j);
				// }
				// }
				// }

				// set the literal value in the new clause the complement of the
				// current assignment
				if (literal.getValue()) {
					literal = literalPool.get(i);
					literal.setValue(false);
				} else {
					literal = literalPool.get(i);
					literal.setValue(true);
				}
				newClause.add(literal);
			}
		}
		if (newClause.getDisjunctiveClause().size() > 0) {
			clausesMasterList.add(newClause);
		}

		return newClause;
	}

	private void backTrack(Clause learntClause) {
		List<Literal> literalsInLearntClause = learntClause.getDisjunctiveClause();
		int backTrackToLevel = 0;

		// finding the second highest level in learnt clause
		int highestLevelLiteral = literalsInLearntClause.get(0).get(), secondHighestLevelLiteral = 0;
		if (literalsInLearntClause.size() > 1) {
			if (literalTracker[literalsInLearntClause.get(1).get()] != literalTracker[highestLevelLiteral]) {
				secondHighestLevelLiteral = literalsInLearntClause.get(1).get();
			}
			if (literalTracker[secondHighestLevelLiteral] > literalTracker[highestLevelLiteral]) {
				highestLevelLiteral = secondHighestLevelLiteral;
				secondHighestLevelLiteral = literalsInLearntClause.get(0).get();
			} 
			backTrackToLevel = literalTracker[secondHighestLevelLiteral];
		}

		if (literalsInLearntClause.size() > 2) {
			for(int i=2; i<literalsInLearntClause.size(); i++) {
				if (literalTracker[literalsInLearntClause.get(i).get()] > literalTracker[secondHighestLevelLiteral]) {
					if (literalTracker[literalsInLearntClause.get(i).get()] > literalTracker[highestLevelLiteral]) {
						secondHighestLevelLiteral = highestLevelLiteral;
						highestLevelLiteral = literalsInLearntClause.get(i).get();
					} else if (literalTracker[literalsInLearntClause.get(i).get()] != literalTracker[highestLevelLiteral] ) {
						secondHighestLevelLiteral = literalsInLearntClause.get(i).get();
					}
				}
			}
			backTrackToLevel = literalTracker[secondHighestLevelLiteral];
		}

		// remove all literal assigned greater than the backtracked level from
		// solution, implication graph, decisionTracker and literalTracker
		for (int i = 1; i <= numLiterals; i++) {
			if (literalTracker[i] >= backTrackToLevel) {
				// remove outgoing edges from literals nodes
				implicationGraph.get(i).clear();
				reverseImplicationGraph.get(i).clear();
				// remove assignment from literals greater than decision level
				// or if the literal is not in the learnt clause
				if (literalTracker[i] > backTrackToLevel || !learntClause.hasLiteral(i)) {
					literalTracker[i] = -1;
					solution.remove(i);
					decisionTracker.put(i, false);
				}
			}
			// remove outgoing edges which are implied greater than or equal to
			// backTrackLevel
			int literal;
			ArrayList<Integer> toRemove = new ArrayList<>();
			ArrayList<Integer> toKeep = new ArrayList<>();
			if (literalTracker[i] < backTrackToLevel) {
				for (int j=0; j<implicationGraph.get(i).size(); j++) {
					literal = implicationGraph.get(i).get(j);
					if (literalTracker[literal] >= backTrackToLevel || literalTracker[literal] == -1) {
						toRemove.add(literal);
					}
				}
				implicationGraph.get(i).removeAll(toRemove);
			}
		}
		// remove conflict
		reverseImplicationGraph.get(0).clear();

		decisionLevel = backTrackToLevel;
	}

	// propagation the implication graph using all the other literals in the
	// clause
	private void addToImplicationGraph(int clauseIndex, Action type) {
		for (Literal literal : clausesMasterList.get(clauseIndex).getDisjunctiveClause()) {
			if (literal.get() != lastAssignedLiteral && type == Action.UNIT_PROPAGATION) {
				if (!implicationGraph.get(literal.get()).contains(lastAssignedLiteral)) {
					implicationGraph.get(literal.get()).add(lastAssignedLiteral);
					reverseImplicationGraph.get(lastAssignedLiteral)
							.add(new ImplicationDetails(literal.get(), clauseIndex));
				}
			} else if (type == Action.CONFLICT) {
				if (!implicationGraph.get(literal.get()).contains(0)) {
					implicationGraph.get(literal.get()).add(0);
					reverseImplicationGraph.get(0).add(new ImplicationDetails(literal.get(), clauseIndex));
				}
			}
		}
	}

	private boolean hasPathToConflict(int literal, boolean[] visited) {

		visited[literal] = true;
		if (visited[lastAssignedLiteral]) {
			return true;
		}

		List<Integer> implications = implicationGraph.get(literal);
		for (int i = 0; i < implications.size(); i++) {
			if (!visited[implications.get(i)]) {
				if (hasPathToConflict(implications.get(i), visited)) {
					return true;
				}
			}
		}
		return false;
	}

	public void printSolution(Action type) {
		Utils.printSolution(type, numLiterals, solution);
	}
}
