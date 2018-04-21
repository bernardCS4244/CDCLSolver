import java.util.Scanner;

public class SatSolver {

	public static void main(String args[]) {
		System.out.print("Input file path: ");
		Scanner sc = new Scanner(System.in);
		String inputFile = sc.next();
		Parser parser = new Parser().parse(inputFile);
		// System.out.println("no of literals: " + parser.getNumLiterals());
		// System.out.println("no of clauses: " + parser.getClauses().size());
		CDCLSolver solver = new CDCLSolver(parser.getNumLiterals(), parser.getClauses());
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
