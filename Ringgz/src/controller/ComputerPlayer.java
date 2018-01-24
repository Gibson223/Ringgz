package controller;

import model.*;

public class ComputerPlayer extends Player {
	
    private Strategy strategy;
    
    public ComputerPlayer(Color color, Strategy strategy, RingList ringList) {
    	super(strategy.getName(), color, ringList);
    	this.strategy = strategy;
    }

	@Override
	public void makeMove(Board board) throws RinggzException {
		int field = strategy.determineField(super.getPrimaryColor()).FieldNumber;
		//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
		Ring ring = new Ring(super.getPrimaryColor(),strategy.determineTier(strategy.determineField(super.getPrimaryColor())));
		board.setRing(field, ring);
	}
}
