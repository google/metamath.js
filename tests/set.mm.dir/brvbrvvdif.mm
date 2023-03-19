include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "cdif.mm"
include "wbr.mm"
include "wn.mm"
include "brvvdif.mm"
include "brvdif.mm"
include "syl6bbr.mm"

theorem brvbrvvdif
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ( ( _V X. _V ) \ R ) B <-> A ( _V \ R ) B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cvv
    cvv
    cxp
    cR
    cdif
    wbr
    cA
    cB
    cR
    wbr
    wn
    cA
    cB
    cvv
    cR
    cdif
    wbr
    cA
    cB
    cR
    cV
    cW
    brvvdif
    cA
    cB
    cR
    brvdif
    syl6bbr
end
