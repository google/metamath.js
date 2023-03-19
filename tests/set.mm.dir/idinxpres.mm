include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "inxpssres.mm"
include "resss.mm"
include "idssxp.mm"
include "ssini.mm"
include "eqssi.mm"

theorem idinxpres
  let cA: class A


  assert |- ( _I i^i ( A X. A ) ) = ( _I |` A )

  proof
    cid
    cA
    cA
    cxp
    #
    cin
    cid
    cA
    cres
    #
    cA
    cA
    cid
    inxpssres
    @1
    cid
    @0
    cid
    cA
    resss
    cA
    idssxp
    ssini
    eqssi
end
