include "wcel.mm"
include "cvv.mm"
include "cop.mm"
include "cxp.mm"
include "elex.mm"
include "opelxpi.mm"
include "syl2an.mm"

theorem opelvvg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> <. A , B >. e. ( _V X. _V ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    cvv
    cvv
    cxp
    wcel
    cB
    cW
    wcel
    cA
    cV
    elex
    cB
    cW
    elex
    cA
    cB
    cvv
    cvv
    opelxpi
    syl2an
end
