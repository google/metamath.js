include "word.mm"
include "cep.mm"
include "wwe.mm"
include "wfr.mm"
include "ordwe.mm"
include "wefr.mm"
include "syl.mm"

theorem ordfr
  let cA: class A


  assert |- ( Ord A -> _E Fr A )

  proof
    cA
    word
    cA
    cep
    wwe
    cA
    cep
    wfr
    cA
    ordwe
    cA
    cep
    wefr
    syl
end
