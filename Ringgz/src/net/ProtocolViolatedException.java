package net;

/**
 * This exception is thrown whenever the protocol (made in project session 1) is
 * somehow violated.
 */
public class ProtocolViolatedException extends Exception {
	
	/**
	 * Message specifying how the protocol was violated.
	 */
	private String message;
	
	/**
	 * Creates a new exception with a given debugging message.
	 * @param message
	 * The message this will be returned in the error message in
	 * <code>getMessage()</code>.
	 */
	public ProtocolViolatedException(String message) {
		this.message = message;
	}
	
	@Override
	public String getMessage() {
		return ("The Ringgz protocol was not followed:\n" + this.message);
	}
}