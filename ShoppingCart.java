import java.util.HashMap;
import java.util.Map;

public class ShoppingCart {

    //@ spec_public
    private int userId;
    //@ spec_public 
    private HashMap<Integer, Item> items;

    //@ public invariant userId >= 0;
    //@ public invariant items != null;
    //@ public invariant (\forall Integer id; items.containsKey(id); id != null && id.intValue() >= 0);
    //@ public invariant (\forall Map.Entry<Integer, Item> entry; items.entrySet().contains(entry); entry.getValue() != null && entry.getValue().getItemId() == entry.getKey().intValue());
    //@ public invariant (\forall Item item; items.values().contains(item); item != null);


    /*@ public normal_behavior
      @ requires userId >= 0;
      @ ensures this.userId == userId;
      @ ensures this.items != null && this.items.isEmpty();
      @*/
    public ShoppingCart(int userId) {
        this.userId = userId;
        this.items = new HashMap<Integer, Item>();
    }

    /*@ public normal_behavior
      @ requires itemId >= 0;
      @ requires quantity > 0;
      @ requires priceInput >= 0.0 && !Double.isNaN(priceInput) && !Double.isInfinite(priceInput);
      @ requires items.containsKey(Integer.valueOf(itemId)) ==> items.get(Integer.valueOf(itemId)).getQuantity() + (\bigint)quantity <= Integer.MAX_VALUE;
      @ ensures items.containsKey(Integer.valueOf(itemId));
      @ ensures \old(items.containsKey(Integer.valueOf(itemId))) ==>
      @      (items.get(Integer.valueOf(itemId)).getQuantity() == \old(items.get(Integer.valueOf(itemId)).getQuantity()) + quantity &&
      @       items.get(Integer.valueOf(itemId)).getPriceDollars() == \old(items.get(Integer.valueOf(itemId)).getPriceDollars()) &&
      @       items.get(Integer.valueOf(itemId)).getPriceCents() == \old(items.get(Integer.valueOf(itemId)).getPriceCents()));
      @ ensures !\old(items.containsKey(Integer.valueOf(itemId))) ==>
      @      (items.get(Integer.valueOf(itemId)).getQuantity() == quantity &&
      @       items.get(Integer.valueOf(itemId)).getItemId() == itemId &&
      @       items.get(Integer.valueOf(itemId)).getPriceDollars() == (int)(Math.round(priceInput * 100.0) / 100L) &&
      @       items.get(Integer.valueOf(itemId)).getPriceCents() == (int)(Math.round(priceInput * 100.0) % 100L));
      @ ensures items.size() == (\old(items.containsKey(Integer.valueOf(itemId))) ? \old(items.size()) : \old(items.size()) + 1);
      @ ensures (\forall Integer otherId; \old(items.containsKey(otherId)) && !otherId.equals(Integer.valueOf(itemId)); items.get(otherId) == \old(items.get(otherId)));
      @ assignable items, items.get(Integer.valueOf(itemId));
      @*/
    public void addItem(int itemId, int quantity, double priceInput) {
        Integer key = Integer.valueOf(itemId);
        if (this.items.containsKey(key)) {
            Item existingItem = this.items.get(key);
            existingItem.increaseQuantity(quantity);
        } else {
            Item newItem = new Item(itemId, quantity, priceInput);
            this.items.put(key, newItem);
        }
    }

    /*@ public normal_behavior
      @ requires itemId >= 0;
      @ ensures !items.containsKey(Integer.valueOf(itemId));
      @ ensures (\forall Integer otherId; \old(items.containsKey(otherId)) && !otherId.equals(Integer.valueOf(itemId)); items.containsKey(otherId) && items.get(otherId) == \old(items.get(otherId)));
      @ assignable items;
      @*/
    public void removeItem(int itemId) {
        this.items.remove(Integer.valueOf(itemId));
    }

    /*@ public normal_behavior
      @ requires itemId >= 0;
      @ requires newQuantity >= 0;
      @ requires newQuantity > 0 ==> items.containsKey(Integer.valueOf(itemId));
      @ ensures newQuantity > 0 ==>
      @      (items.containsKey(Integer.valueOf(itemId)) &&
      @       items.get(Integer.valueOf(itemId)).getQuantity() == newQuantity &&
      @       items.get(Integer.valueOf(itemId)).getPriceDollars() == \old(items.get(Integer.valueOf(itemId)).getPriceDollars()) &&
      @       items.get(Integer.valueOf(itemId)).getPriceCents() == \old(items.get(Integer.valueOf(itemId)).getPriceCents()));
      @ ensures newQuantity == 0 ==> !items.containsKey(Integer.valueOf(itemId));
      @ ensures (\forall Integer otherId; \old(items.containsKey(otherId)) && !otherId.equals(Integer.valueOf(itemId)); items.containsKey(otherId) && items.get(otherId) == \old(items.get(otherId)));
      @ assignable items, items.get(Integer.valueOf(itemId));
      @*/
     public void updateQuantity(int itemId, int newQuantity) {
        Integer key = Integer.valueOf(itemId);
        if (newQuantity > 0) {
            Item item = this.items.get(key);
            if (item != null) {
                item.setQuantity(newQuantity);
            }
        } else {
            this.items.remove(key);
        }
     }

    /*@ public normal_behavior
      @ ensures \result >= 0L;
      @ ensures (\sum Integer id; items.containsKey(id);
             items.get(id).getTotalPriceInCents() * items.get(id).getQuantity()) <= Long.MAX_VALUE;
      @ assignable \nothing;
      @ measured_by items.size();
      @*/
    public /*@ pure @*/ long getTotal() {
        long grandTotalCents = 0L;

        //@ maintaining grandTotalCents >= 0L;
        //@ maintaining grandTotalCents <= Long.MAX_VALUE;
        // @ maintaining (\bigint)grandTotalCents == (\sum Item it; /* complex range definition */; (\bigint)it.getTotalPriceInCents() * (\bigint)it.getQuantity());
        // @ decreasing /* some valid expression */;
        for (Item item : items.values()) {
             long itemUnitPriceCents = item.getTotalPriceInCents();
             int itemQuantity = item.getQuantity();
             long itemTotalCents = itemUnitPriceCents * itemQuantity;
             grandTotalCents += itemTotalCents;
        }
        return grandTotalCents;
    }

    /*@ public normal_behavior
      @ ensures \result != null;
      @ ensures \result == this.items;
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ HashMap<Integer, Item> prepareForCheckout() {
        return this.items;
    }

    private static String formatCents(long totalCents) {
        long dollars = totalCents / 100;
        long cents = totalCents % 100;
        return "$" + dollars + "." + String.format("%02d", cents);
    }

     public static void main(String[] args) {
         ShoppingCart cart = new ShoppingCart(1);
         System.out.println("Initial Total: " + formatCents(cart.getTotal()));

         cart.addItem(101, 2, 19.99);
         cart.addItem(102, 1, 5.50);
         System.out.println("After adds: " + formatCents(cart.getTotal()));

         cart.addItem(101, 1, 19.99);
         System.out.println("After add existing: " + formatCents(cart.getTotal()));

         cart.updateQuantity(101, 1);
         System.out.println("After updateQ(101, 1): " + formatCents(cart.getTotal()));

         cart.removeItem(102);
         System.out.println("After remove(102): " + formatCents(cart.getTotal()));

         cart.updateQuantity(101, 0);
         System.out.println("After updateQ(101, 0): " + formatCents(cart.getTotal()));
         System.out.println("Cart empty? " + cart.items.isEmpty());

         cart.addItem(301, 1, 10.005);
         cart.addItem(302, 1, 10.0049);
         System.out.println("After rounding tests: " + formatCents(cart.getTotal()));

         HashMap<Integer, Item> checkoutData = cart.prepareForCheckout();
         System.out.println("Data for checkout size: " + checkoutData.size());
     }
}