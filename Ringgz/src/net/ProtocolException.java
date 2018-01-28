package net;

/**
 * This exception is thrown whenever the protocol (made in project session 1) is
 * somehow violated.
 */
public class ProtocolException extends Exception {

	private String message;

	// Creates a new exception with a given debugging message.
	public ProtocolException(String message) {
		this.message = message;
	}

	@Override
	public String getMessage() {
		return ("The protocol was violated:\n" + this.message);
	}
}