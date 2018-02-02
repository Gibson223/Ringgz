package controller;

import model.Board;

public class ServerPlayer extends Player {
	public ServerPlayer(String name) {
		super(name);
	}
	@Override
	public void makeMove(Board board) throws RinggzException {
		// TODO needs to depend on the input to the server of that specific client. i
		// think we need to assign
		// the inputstream of that client socket to this???
	}
}
