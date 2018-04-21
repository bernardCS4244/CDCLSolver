import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class Parser {
	private List<Clause> clauses;
	private String line;
	private int numLiterals;
	private int numClauses;

	public Parser() {
		line = "";
		numLiterals = 0;
		numClauses = 0;
	}

	public Parser parse(String inputFile) {
		try (BufferedReader br = new BufferedReader(new FileReader(inputFile))) {
			while ((line = br.readLine()) != null) {
				if (line.length() > 0 && line.charAt(0) == 'p') {
					String[] input = line.split("\\s+");
					numLiterals = Integer.parseInt(input[2]);
					numClauses = Integer.parseInt(input[3]);
					break;
				}
			}
			readFormula(br);

		} catch (FileNotFoundException e) {
			System.out.println("File not found!");
		} catch (IOException e) {
			e.printStackTrace();
		}
		return this;
	}

	private void readFormula(BufferedReader br) {
		clauses = new ArrayList<>();
		int counter = numClauses;

		try {
			while (counter != 0) {
				clauses.add(readClause(br.readLine()));
				counter--;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private Clause readClause(String clauseString) {
		Clause clause = new Clause();
		String[] literalArray = clauseString.split("\\s+");
		for (int i = 0; i < literalArray.length; i++) {
			if (!literalArray[i].equals("")) {
				int literal = Integer.parseInt(literalArray[i]);
				if (literal > 0) {
					clause.add(new Literal(literal, true));
				} else if (literal < 0) {
					clause.add(new Literal(literal * -1, false));
				}
			}
		}
		return clause;
	}

	public int getNumLiterals() {
		return numLiterals;
	}

	public List<Clause> getClauses() {
		if (clauses == null) {
			clauses = new ArrayList<Clause>();
		}
		return clauses;
	}

}
