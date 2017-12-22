
public class Ring {
	
	public enum RingType {
		TIER1, TIER2, TIER3, TIER4, BASE, NULL
	}
	
	//CHECKS IF THE CHOSEN RING IS A VALID CHOICE IN THE ENUM ABOVE
	//@ensures TODO
	//TODO: SOMETHING TO TURN THE INPUT STRING INTO A (RingType choice)
	public static boolean isRing(RingType choice) {
		   for(RingType aType : RingType.values()) {
		      if(aType == choice) {
		         return true;
		      }
		   }
		   return false;
		}
	
	//TODO
	public Ring getRing() {
		return this.RingType;
	}
}
