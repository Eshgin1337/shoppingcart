# Shopping Cart JML Project - How to Run

Minimal instructions assuming your Java JDK and OpenJML bundle are set up.

## Prerequisites

* Java JDK 21+ (`javac`, `java` commands available - version 21.0.6 used in testing)
* OpenJML bundle (version **21-0.6** for Ubuntu/Java 21 used in testing) unzipped, providing the `openjml` script.

## Assumed Structure

It's assumed you are running commands from a root directory containing:
1.  The `openjml` script (and its associated `lib/` etc. directories from the bundle).
2.  A subdirectory named `shoppingcart/` which contains `Item.java` and `ShoppingCart.java`.

```text
project_root/
├── openjml          <-- The script from the bundle
├── lib/             <-- OpenJML libs from bundle
├── (other_openjml_files)/
├── shoppingcart/
│   ├── Item.java
│   └── ShoppingCart.java
└── README.md       
```

## Steps (Run from `project_root`)

1.  **Compile Java Code:**
    ```bash
    javac -sourcepath shoppingcart shoppingcart/ShoppingCart.java
    ```
    (This creates `.class` files inside `shoppingcart/`)

2.  **Run Test `main` Method (Optional):**
    ```bash
    cd shoppingcart; java ShoppingCart; cd ../
    ```
    (Requires `main` method in `ShoppingCart.java`)

3.  **Run OpenJML Syntax/Type Check:**
    ```bash
    ./openjml -sourcepath shoppingcart -check shoppingcart/ShoppingCart.java
    ```

4.  **Run OpenJML Static Verification (ESC):**
    ```bash
    ./openjml -sourcepath shoppingcart -esc shoppingcart/ShoppingCart.java
    ```

*(Note: Adjust paths if your `openjml` script or `shoppingcart` directory are located differently relative to where you run the commands.)*
