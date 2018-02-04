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
		if (this.clienthandler == null) {
			return this.move;
		} else {
			return this.clienthandler.getMove();
		}
	}

	public boolean moveread;
	private Move move;

	public void setMove(Move move) {
		this.move = move;
	}

}
