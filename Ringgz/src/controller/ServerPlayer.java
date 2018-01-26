package controller;

import java.io.IOException;
import java.io.InputStream;
import java.net.Socket;

import model.Board;
import model.Color;
import model.RingList;

public class ServerPlayer extends Player{
	public InputStream in;
	public ServerPlayer(String name, Color color, RingList ringList, Socket clientSocket) {
		super(name);
		try {
			this.in = clientSocket.getInputStream();//i think we have to do something like this
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	@Override
	public void makeMove(Board board) throws RinggzException {
		//TODO needs to depend on the input to the server of that specific client. i think we need to assign
		//the inputstream of that client socket to this???
		
	}

}
