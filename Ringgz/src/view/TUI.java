package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Observable;
import java.util.Observer;

import model.Board;
import model.Field;

//TUI for Ringgz
public class TUI implements Observer, Runnable {

	private Board board;

	public static final String EXIT = "exit";

	// Creates a TUI with the given Game
	public TUI() {
		this.INIT();
	}

	public void INIT() {
		this.output(("Insert username and IP separated by a space"));
	}

	public Object[] initizializing() {
		String username = null;
		String address = null;
		boolean correct = false;
		while (!correct) {
			Object input = this.TUIInput("-");
			Object[] splitInput = ((String) input).split(" ");
			correct = true;
			if (splitInput.length != 2) {
				correct = false;
				this.output(("Two arguments are needed. Please try again."));
			}
			username = (String) splitInput[0];
				address = (String) splitInput[1];
		}
		return new Object[] { username, address };
	}
	public String TUIInput(String string) {
		String response = null;
		System.out.println(string);
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			response = in.readLine();
		} catch (IOException e) {
		}
		if (response == null) {
			return TUIInput(string);
		} else {
			return response;
		}
	}
	public void output (String message) {
		System.out.println(message);
	}

	public void view() {
		for (Field field : board.fields) {
			if (((field.FieldNumber - 1) % 5) == 0) {
				System.out.print("\n\n" + "|");
			}
			System.out.print(field.toString() + "|");
		}
	}

	public void run() {
		this.view();
	}

	@Override
	public void update(Observable arg0, Object arg1) {
		this.view();
	}
}