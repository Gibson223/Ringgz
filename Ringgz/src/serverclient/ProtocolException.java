package serverclient;

/**
 * This exception is thrown whenever the protocol (made in project session 1) is
 * somehow violated.
 */
public class ProtocolException extends Exception {

	// Creates a new exception with a given debugging message.
	public ProtocolException(String message) {
		super(message);
	}
}