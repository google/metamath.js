include "wss.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cpred.mm"
include "ssrin.mm"
include "df-pred.mm"
include "3sstr4g.mm"

theorem predpredss
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( A C_ B -> Pred ( R , A , X ) C_ Pred ( R , B , X ) )

  proof
    cA
    cB
    wss
    cA
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    cB
    @0
    cin
    cA
    cR
    cX
    cpred
    cB
    cR
    cX
    cpred
    cA
    cB
    @0
    ssrin
    cA
    cR
    cX
    df-pred
    cB
    cR
    cX
    df-pred
    3sstr4g
end
