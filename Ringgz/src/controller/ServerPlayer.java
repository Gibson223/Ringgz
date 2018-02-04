package controller;

import model.Board;
import serverclient.ClientHandler;

public class ServerPlayer extends Player {
	public ClientHandler clienthandler;
	public ServerPlayer(String name, ClientHandler clienthandler) {
		super(name);
		this.clienthandler = clienthandler;
		moveread = false;
	}
	public ServerPlayer(String name) {
		super(name);
	}
	@Override
	public Move makeMove(Board board) throws RinggzException {
		return this.clienthandler.getMove();
		// TODO needs to depend on the input to the server of that specific client. i
		// think we need to assign
		// the inputstream of that client socket to this???
	}
	public boolean moveread;
	private Move move;
	public void setMove(Move move) {
		this.move = move;
	}
	
}
