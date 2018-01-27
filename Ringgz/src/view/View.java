package view;


public interface View extends Runnable {
	
	public void displayStartupState();
	public void displayConnectingState();
	public void displayConnectedState();
	public void displayLobbyState();
	public void displayGameState();
	public void displayGameMovingState();
	public void displayPostGameState();
	public void displayError(String error);
	public void setViewState(ViewState viewState);
	public ViewState getViewState();
	
	//THESE METHODS ARE CALLED WHEN SOMETHING HAPPENS WHICH REQUIRES THE VIEW TO BE UPDATED
	public void waitingInLobby();
	public boolean allPlayersConnected();
	public void onGameStarted();
	public void otherMoves();
	public void gameFinished();
	public Object[] getArguments();
	public void onConnectionAccepted();
	public void onConnectionDeclined();
	public Object[] getGameRequest();

	
	public static enum ViewState {
		STARTUP,
		CONNECTING,
		CONNECTED,
		LOBBY,
		GAME,
		GAME_MOVING,
		POST_GAME
		;
	}
}