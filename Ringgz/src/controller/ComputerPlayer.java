package controller;

import model.*;

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
	public void makeMove(Board board) {
		int field = strategy.determineField(super.getPrimaryColor()).FieldNumber;
		//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
		Ring ring = new Ring(super.getPrimaryColor(),strategy.determineTier(strategy.determineField(super.getPrimaryColor())));
		board.setRing(field, ring);
	}
}
