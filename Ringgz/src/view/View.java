package view;


public interface View extends Runnable {
	
	public void StartupState();
	public void ConnectingState();
	public void ConnectedState();
	public void PostGameState();
	public void Error(String error);
	public void setViewState(ViewState viewState);
	public ViewState getViewState();
	
	//THESE METHODS ARE CALLED WHEN SOMETHING HAPPENS WHICH REQUIRES THE VIEW TO BE UPDATED
	public void waitingInLobby();
	public boolean allPlayersConnected();
	public void onGameStarted();
	public void awaitingMoves();
	public void gameFinished();
	public Object[] getArguments();
	public void onConnectionAccepted();
	public void onConnectionDeclined();
	public Object[] getGameRequest();

	
	public static enum ViewState {
		STARTUP,
		CONNECTING,
		CONNECTED,
		POST_GAME
		;
	}
}