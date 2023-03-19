include "cvv.mm"
include "cdif.mm"
include "wbr.mm"
include "wn.mm"
include "brv.mm"
include "brdif.mm"
include "mpbiran.mm"

theorem brvdif
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A ( _V \ R ) B <-> -. A R B )

  proof
    cA
    cB
    cvv
    cR
    cdif
    wbr
    cA
    cB
    cvv
    wbr
    cA
    cB
    cR
    wbr
    wn
    cA
    cB
    brv
    cA
    cB
    cvv
    cR
    brdif
    mpbiran
end
