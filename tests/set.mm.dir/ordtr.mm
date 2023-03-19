include "word.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "df-ord.mm"
include "simplbi.mm"

theorem ordtr
  let cA: class A


  assert |- ( Ord A -> Tr A )

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
    simplbi
end
