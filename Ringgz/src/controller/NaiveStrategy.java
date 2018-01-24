package controller;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import model.Board;
import model.Color;
import model.Ring;
import model.Tier;

public class NaiveStrategy implements Strategy {

	@Override
	public String getName() {
		return "Naive";
	}

	@Override
	public int determineMove(Board b, Ring r) {
		List<Integer> availableList = new ArrayList<>();
		for (int i = 0; i < Board.DIM*Board.DIM; i++) {
			if (b.isAllowed(i,r.getColor())) {
				availableList.add(i);
			}
		}
		Collections.shuffle(availableList);
		return availableList.get(0);
	}
}
