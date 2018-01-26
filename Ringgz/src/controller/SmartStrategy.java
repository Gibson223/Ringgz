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
	public Field determineField(Board board, Player p) {
		if (board.firstMove) {
			try {
				p.potentialFields.addAll(Arrays.asList(board.getField(7), board.getField(8), board.getField(9), board.getField(12), board.getField(13), board.getField(14), board.getField(17), board.getField(18), board.getField(19)));
				boolean fieldFound = false;
				while (!fieldFound) {
					Collections.shuffle(p.potentialFields);
					Field smartField = p.potentialFields.get(0);
					int frec = Collections.frequency(smartField.getFieldColors(),p.getPrimaryColor());
					if (frec > 2) {
						determineField(board,p);
					} else {
						fieldFound = true;
						return smartField;
					}
				}
			} catch (RinggzException e) {
				e.printStackTrace();
			}
		} else {
			boolean fieldFound = false;
			while (!fieldFound) {
				Collections.shuffle(p.potentialFields);
				Field smartField = p.potentialFields.get(0);
				int frec = Collections.frequency(smartField.getFieldColors(),p.getPrimaryColor());
				if (frec > 2) {
					determineField(board,p);
				} else {
					fieldFound = true;
					return smartField;
				}
			}
		}
	}

	@Override
	public Tier determineTier(Field f) {
		// TODO Auto-generated method stub
		return null;
	}
}


