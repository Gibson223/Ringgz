package view;


public interface View extends Runnable {
	
	public static enum ViewType {
		STARTUP, CONNECTING, CONNECTED,	POST_GAME
	}
	
	public void Initial();
	public void Connecting();
	public void Connected();
	public void GameOver();
	public void Error(String error);
	public void setViewType(ViewType type);
	public ViewType getViewType();
	
	public void inLobby();
	public boolean allConnected();
	public void onGameStarted();
	public void awaitingMoves();
	public void gameFinished();
	public Object[] getArguments();
	public void onConnectionAccepted();
	public void onConnectionDeclined();
	public Object[] getGameRequest();
}