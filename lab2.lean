import PnP2023.Labs.Lab02.SelectionSort

def sortedList(l : List ℕ) : 
    {l' : List ℕ // l'.sorted ∧ ∀ a: ℕ, a ∈ l ↔ a ∈  l'} := ⟨selectionSort l, selectionSort_sorted l, by apply selectionSort_mem⟩

def main : IO Unit :=
  IO.println <| sortedList [20, 3, 7, 7, 8, 9, 10]

