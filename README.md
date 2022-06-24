# Automated Modal Correspondence
## General
This project has been implemented for a Bachelor's Thesis at the University of Amsterdam. It is an implementation of the Sahlqvist-van Benthem Algorithm, which computes local first-order correspondents of modal formulas that have certain syntactic characteristics. To engage with this product, one needs to have Haskell as well as a compiler such as GHCi installed. Use the 'stack ghci' command in the project folder to load all files.

## Input
The user interactions occur in the Main.hs file. When all files are loaded in the compliler, one can access this by entering 'main' in the terminal. At this point, the user can enter a modal formula as input.

The following conventions are used to enter modal formulas (commas signify different options):

Actual | Input
--- | ---
Proposition | p, q, r
Top | Top
Bot | Bot
Negation | ~, Not, not
Conjunction | &
Disjunction | \|
Implication | ->
Bi-implication | iff
Box | []
Diamond | <>
Brackets | (, )

Use brackets to ensure the modal input formula is parsed as intended. Using tokens outside of this table will result in lexing errors. Incorrect modal syntax will result in a parsing error. 

Provided a correct modal formula as input. The program will first return that formula such that the user is made aware of possibly ambiguous parses.

## Output
For any modal formula, the program outputs the following:
- Whether the formula is **Sahlqvist**
- Whether the formula is **uniform**
- If _possible_, a **first-order correspondent**
    - Otherwise a notification that no correspondent can be found.
    - If _possible_, a **visualization** of the local frame property

If the formula is Sahlqvist or uniform, a first-order correspondent will always be computed. If a first-order correspondent is computable, a visualization is given provided some conditions on the complexity of the frame property.

### Interpreting the Visualizations


ADDING IMAGES
![alt text](https://github.com/[username]/[reponame]/blob/[branch]/image.jpg?raw=true)