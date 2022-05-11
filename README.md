# Eazy Język Funkcyjny

Wszystkie konstrukcje w języku Eazy są typowe i niewymagające elaboracji.

* Infiksowe operatory arytmetyczne: `+, -, *, /`
* Infiksowe operatory logiczne: `&&, ||, ==, =/=, <, >, <=, >=`
* Operator arytmetycznej zmiany znaku: `-`
* Operator logiczny: `~`
* Konstrukcja "IF": `(wyrażenie) if (warunek) otherwise (wyrażenie)`
* Konstrukcja "MATCH": `match (wyrażenie) with { (wzorzec -> wyrażenie)+ }`
    * We wzorcu dopuszczalna jest konstrukcja `wzorzec as id`
* Konstrukcja "LET": `let { (deklaracje) } in (wyrażenie)`
* Funkcje anonimowe: `lambda{ (typ) } (parametry) -> (wyrażenie)`
* Konsntrukcja list: `[ (wyrażenia) ], głowa :: ogon`
* Deklarowanie typu funkcji: `(nazwa) : (typ)`
* Tworzenie nowych typów: `type (Nazwa) (parametry) = (Opcja1) (parametry) | (Opcja2) (parametry) | ...`
* Komentarze: `;) (treść) (;, ;* (treść)`

Zrealizowane podpunkty:
+  01 (dwa typy)
+  02 (arytmetyka, porównania)
+  03 (if)
+  04 (funkcje wieloargumentowe, rekurencja)
+  05 (funkcje anonimowe i wyższego rzędu, częściowa aplikacja)
+  06 (obsługa błędów wykonania)
+  07 (statyczne wiązanie identyfikatorów)
+  08 (z pattern matchingiem)  
+  10 (lukier)
+  11 (listy dowolnego typu, zagnieżdżone i listy funkcji)
+  12 (proste typy algebraiczne z jednopoziomowym pattern matchingiem)
+  13 (statyczne typowanie)
+  14 (ogólne polimorficzne i rekurencyjne typy algebraiczne)
+  15 (zagnieżdżony pattern matching)

Dodatkowo w języku pojawiły się eksperymentalnie funkcje polimorficzne.

