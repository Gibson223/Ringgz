package net;

/**
 * This exception is thrown whenever the protocol (made in project session 1) is
 * somehow violated.
 */
public class ProtocolViolatedException extends Exception {

	private String message;

	// Creates a new exception with a given debugging message.
	public ProtocolViolatedException(String message) {
		this.message = message;
	}

	@Override
	public String getMessage() {
		return ("The protocol was violated:\n" + this.message);
	}
}