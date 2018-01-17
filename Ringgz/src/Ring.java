
public class Ring {
	private Color color;
	private Tier tier;
	Ring(Color c, Tier t){
		color = c;
		tier = t;
	}
	public void setTier(Tier tier) {
		this.tier = tier;
	}
	public Tier getTier() {
		return tier;
	}
	public Color getColor() {
		return color;
	}
	public void setColor(Color color) {
		this.color = color;
	}
//	//CHECKS IF THE CHOSEN RING IS A VALID CHOICE IN THE ENUM ABOVE
//	//@ensures TODO
//	//TODO: SOMETHING TO TURN THE INPUT STRING INTO A (RingType choice)
//	public static boolean isRing(RingType choice) {
//		   for(RingType aType : RingType.values()) {
//		      if(aType == choice) {
//		         return true;
//		      }
//		   }
//		   return false;
//		}
//	
}
