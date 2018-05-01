import java.util.Scanner;

public class SatSolver {

	public static void main(String args[]) {
		System.out.print("Input file path: ");
		Scanner sc = new Scanner(System.in);
		String inputFile = sc.next();
		Parser parser = new Parser().parse(inputFile);
		CDCLSolver solver = new CDCLSolver(parser.getNumLiterals(), parser.getClauses(), 
				CDCLSolver.DecisionHeuristicType.DYNAMIC, CDCLSolver.ConflictAnalysisType.UIP);
		Action result = solver.solve();
		switch (result) {
		case SAT:
			System.out.println("SAT");
			solver.printSolution(Action.SAT);
			break;
		case UNSAT:
			System.out.println("UNSAT");
			solver.printSolution(Action.UNSAT);
		}
	}
}
