include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "wbr.mm"
include "ididg.mm"
include "reli.mm"
include "brrelexi.mm"
include "impbii.mm"

theorem issetid
  let cA: class A


  assert |- ( A e. _V <-> A _I A )

  proof
    cA
    cvv
    wcel
    cA
    cA
    cid
    wbr
    cA
    cvv
    ididg
    cA
    cA
    cid
    reli
    brrelexi
    impbii
end
