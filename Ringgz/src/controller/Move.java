package controller;

public class Move {
	public final int x;
	public final int y; 
	public final int moveType;
	public final int color;
	public Move(int x, int y, int moveType, int color) {
		this.x = x;
		this.y = y;
		this.moveType = moveType;
		this.color = color;
	}
}