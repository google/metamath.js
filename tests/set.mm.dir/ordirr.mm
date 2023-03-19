include "word.mm"
include "cep.mm"
include "wfr.mm"
include "wcel.mm"
include "wn.mm"
include "ordfr.mm"
include "efrirr.mm"
include "syl.mm"

theorem ordirr
  let cA: class A


  assert |- ( Ord A -> -. A e. A )

  proof
    cA
    word
    cA
    cep
    wfr
    cA
    cA
    wcel
    wn
    cA
    ordfr
    cA
    efrirr
    syl
end
