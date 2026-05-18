import Comparator.Answer
set_option comparator.answer "with_auxiliary"
theorem foo : answer((42 : Nat)) = 42 := rfl
