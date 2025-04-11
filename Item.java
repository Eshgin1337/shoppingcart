public class Item {

    //@ spec_public
    private int itemId;
    //@ spec_public
    private int quantity;
    //@ spec_public
    private int priceDollars;
    //@ spec_public
    private int priceCents;

    //@ public invariant itemId >= 0;
    //@ public invariant quantity >= 0;
    //@ public invariant priceDollars >= 0;
    //@ public invariant priceCents >= 0 && priceCents <= 99;

    /*@ public normal_behavior
      @ requires itemId >= 0;
      @ requires quantity >= 0;
      @ requires priceInput >= 0.0 && !Double.isNaN(priceInput) && !Double.isInfinite(priceInput);
      @ ensures this.itemId == itemId;
      @ ensures this.quantity == quantity;
      @ ensures priceDollars == (int) (Math.round(priceInput * 100.0) / 100L);
      @ ensures priceCents == (int) (Math.round(priceInput * 100.0) % 100L);
      @*/
    public Item(int itemId, int quantity, double priceInput) {
        if (priceInput < 0.0 || Double.isNaN(priceInput) || Double.isInfinite(priceInput)) {
            throw new IllegalArgumentException("Price input must be non-negative and finite.");
        }
        this.itemId = itemId;
        this.quantity = quantity;
        long totalCents = Math.round(priceInput * 100.0);
        this.priceDollars = (int) (totalCents / 100L);
        this.priceCents = (int) (totalCents % 100L);
    }

    /*@ public normal_behavior
      @ ensures \result == this.quantity;
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ int getQuantity() {
        return this.quantity;
    }

    /*@ public normal_behavior
      @ ensures \result == this.itemId;
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ int getItemId() {
        return this.itemId;
    }

    /*@ public normal_behavior
      @ ensures \result == this.priceDollars;
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ int getPriceDollars() {
        return this.priceDollars;
    }

    /*@ public normal_behavior
      @ ensures \result == this.priceCents;
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ int getPriceCents() {
        return this.priceCents;
    }

    /*@ public normal_behavior
      @ ensures \result == (long)this.priceDollars * 100L + this.priceCents;
      @ ensures \result == (\bigint)this.priceDollars * 100 + (\bigint)this.priceCents;
      @ ensures \result >= 0;
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ long getTotalPriceInCents() {
        long totalCents = (long) this.priceDollars * 100L + this.priceCents;
        return totalCents;
    }

    /*@ public normal_behavior
      @ requires newQuantity >= 0;
      @ ensures this.quantity == newQuantity;
      @ assignable this.quantity;
      @*/
    public void setQuantity(int newQuantity) {
        this.quantity = newQuantity;
    }

    /*@ public normal_behavior
      @ requires amount > 0;
      @ requires (\bigint)this.quantity + (\bigint)amount <= Integer.MAX_VALUE;
      @ ensures this.quantity == \old(this.quantity) + amount;
      @ assignable this.quantity;
      @*/
    public void increaseQuantity(int amount) {
        this.quantity += amount;
    }
}