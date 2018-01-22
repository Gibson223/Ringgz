package controller;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import model.Board;
import model.Color;
public class NaiveStrategy implements Strategy {

	@Override
	public String getName() {
		return "Naive";
	}

	@Override
	public int determineMove(Board b, Color c) {
		List<Integer> availableList = new ArrayList<>();
		for (int i = 0; i < Board.DIM*Board.DIM; i++) {
			if (b.proximityCheck(i,c)) {
				availableList.add(i);
			}
		}
		Collections.shuffle(availableList);
		return availableList.get(0);
	}
}
