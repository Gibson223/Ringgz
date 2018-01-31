package controller;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.Tier;

public class SmartStrategy implements Strategy {

	public String getName() {
		return "Smart";
	}

	@Override
	public Field determineField(Board board, Player p) {
		p.potentialFields.clear();
		List<Field> fields = new LinkedList<Field>();
		for (Field field: board.fields) {
			if (field.getFieldState().stream().anyMatch(a -> a.getColor() == p.getPrimaryColor())) {
				p.potentialFields.add(field);
			}
		}
		
		if (board.firstMove) {
			Collections.shuffle(board.middle9);
			try {
				return board.getField((board.middle9.get(0)));
			} catch (RinggzException e) {
				determineField(board, p);
				e.printStackTrace();
			}
		} 
		Collections.shuffle(p.potentialFields);
		Field smartField = p.potentialFields.get(0);
		boolean fieldFound = false;
		while (!fieldFound) {
			int frec = Collections.frequency(smartField.getFieldColors(), p.getPrimaryColor());
			if (frec > 2) {
				determineField(board, p);
			} else {
				fieldFound = true;
			}
		}
		return smartField;
		}

	@Override
	public Tier determineTier(Board board, Field f, Player p) {
		List<Tier> availableTiers = new ArrayList<>();
		for (Ring ring : f.getFieldState()) {
			if (ring.getColor() == Color.INIT) {
				availableTiers.add(ring.getTier());
			}
		}
		try {
			Collections.shuffle(availableTiers);
			return availableTiers.get(0);
		} 
		catch (IndexOutOfBoundsException e) {
			return determineTier(board, this.determineField(board, p), p);
		}
	}

	@Override
	public Color determineColor(Board board, Player p) {
		List<Color> colors = new ArrayList<>();
		colors.add(p.getPrimaryColor());
		colors.add(p.getSecondaryColor());
		Collections.shuffle(colors);
		return colors.get(0);
	}

	@Override
	public Object[] determineMove() {
		
		return null;
	}

}
