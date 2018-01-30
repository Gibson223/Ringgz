package view;

public interface View extends Runnable {

	public static enum ViewType {
		START, CONNECTING, CONNECTED, POST_GAME
	}

	public void Initial();

	public void Connecting();

	public void Connected();

	public void GameOver();

	public void Error(String error);
	
	public ViewType getViewType();

	public void setViewType(ViewType type);

	public void inLobby();

	public boolean allConnected();

	public void startGame();

	public void awaitingMoves();

	public void gameFinished();

	public Object[] getArguments();

	public void accepted();

	public void denied();

	public Object[] getGameRequest();
}