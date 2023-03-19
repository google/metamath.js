include "wss.mm"
include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "inxpssres.mm"
include "a1i.mm"
include "idresssidinxp.mm"
include "eqssd.mm"

theorem idreseqidinxp
  let cA: class A
  let cB: class B


  assert |- ( A C_ B -> ( _I i^i ( A X. B ) ) = ( _I |` A ) )

  proof
    cA
    cB
    wss
    #
    cid
    cA
    cB
    cxp
    cin
    #
    cid
    cA
    cres
    #
    @1
    @2
    wss
    @0
    cA
    cB
    cid
    inxpssres
    a1i
    cA
    cB
    idresssidinxp
    eqssd
end
