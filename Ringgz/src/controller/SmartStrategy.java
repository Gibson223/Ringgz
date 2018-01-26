package controller;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import model.Board;
import model.Color;
import model.Field;
import model.Tier;

public class SmartStrategy implements Strategy{

	@Override
	public String getName() {
		return "Smart";
	}
	
	@Override
	public Field determineField(Board board, Color c) {
		if (board.firstMove) {
			try {
				potentialFields.addAll(Arrays.asList(board.getField(7), board.getField(8), board.getField(9), board.getField(12), board.getField(13), board.getField(14), board.getField(17), board.getField(18), board.getField(19)));
			} catch (RinggzException e) {
				e.printStackTrace();
			}
		}
		boolean fieldFound = false;
		while (!fieldFound) {
			Collections.shuffle(potentialFields);
			Field smartField = potentialFields.get(0);
			int frec = Collections.frequency(smartField.getFieldColors(),c);
			if (frec > 2) {
				determineField(board,c);
			} else {
				fieldFound = true;
				return smartField;
			}
		}	
	}

	@Override
	public Tier determineTier(Field f) {
		// TODO Auto-generated method stub
		return null;
	}
}


