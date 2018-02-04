package model;

public class Ring {
    public Color color;
    public Tier tier;

    //@requires c != null && t != null;
    //@ensures this.getColor() == c && this.getTier() == t;
    public Ring(Color c, Tier t) {
        color = c;
        tier = t;
    }

    //@requires this.color != null;
    //@requires this.tier != null;
    //@ensures this.color == this.getColor();
    //@ensures this.tier == this.getTier();
    public Ring() {
        color = Color.INIT;
        tier = Tier.INIT;
    }

    //@requires tier != null;
    //@ensures tier == this.getTier();
    public void setTier(Tier tier) {
        this.tier = tier;
    }

    //@ensures \result != null;
    //@pure
    public Tier getTier() {
        return tier;
    }

    //@ensures \result != null;
    //@pure
    public Color getColor() {
        return color;
    }

    //@requires color != null;
    //@ensures this.getColor() == color;
    public void setColor(Color color) {
        this.color = color;
    }

    // CHECKS IF THE CHOSEN RING IS A VALID CHOICE
    //@requires choice != null;
    //@pure
    public static boolean isRing(Tier choice) {
        for (Tier aType : Tier.values()) {
            if (aType == choice) {
                return true;
            }
        }
        return false;
    }

    @Override
    //@pure
    public boolean equals(Object ring) {
        if (ring instanceof Ring && ((Ring) ring).getColor() == this.getColor()
                && ((Ring) ring).getTier() == this.getTier()) {
            return true;
        }
        return false;

    }

    // returns the color of the ring in a String
    @Override
    public String toString() {
        return this.getColor().toString();
    }
}
