package controller;
import java.util.*;

import model.Board;
import model.Color;

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
	public List<Integer> determineMove(Board board) {
		List <Integer> result = new LinkedList<>();
		result.add((strategy.determineField(super.getPrimaryColor())).FieldNumber);
		result.add((strategy.determineTier(strategy.determineField(super.getPrimaryColor())).FieldNumber));

	}
}
