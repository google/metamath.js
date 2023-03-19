include "word.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "df-ord.mm"
include "simprbi.mm"

theorem ordwe
  let cA: class A


  assert |- ( Ord A -> _E We A )

  proof
    cA
    word
    cA
    wtr
    cA
    cep
    wwe
    cA
    df-ord
    simprbi
end
