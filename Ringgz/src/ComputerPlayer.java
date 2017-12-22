

public class ComputerPlayer extends Player {
	
    private Strategy strategy;
    
    public ComputerPlayer(Color color, Strategy strategy) {
    	super(strategy.getName(), color);
    	this.strategy = strategy;
    }
    
    public ComputerPlayer(Color color) {
    	this(color, new NaiveStrategy());
    }

	@Override
	public int determineMove(Board board) {
		return strategy.determineMove(board, getColor());
	}
}
