package controller;

import model.Tier;

public class Move {
	public final int x;
	public final int y; 
	public final int moveType;
	public final String color;
	public Move(int x, int y, int moveType, String color) {
		this.x = x;
		this.y = y;
		this.moveType = moveType;
		this.color = color;
	}
	public int getX() {
		return this.x;
	}
	public int getY() {
		return this.y;
	}
	public Tier getMoveType() {
		return Tier.toTier(moveType);
	}
	public String getColor() {
		return color;
	}
}