

public interface Strategy {
	
	public String getName();
	public int determineMove(Board b, Color c);

}