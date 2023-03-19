include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "cin.mm"
include "df-res.mm"
include "inss2.mm"
include "eqsstri.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"

theorem relres
  let cA: class A
  let cB: class B


  assert |- Rel ( A |` B )

  proof
    cA
    cB
    cres
    #
    cB
    cvv
    cxp
    #
    wss
    @1
    wrel
    @0
    wrel
    @0
    cA
    @1
    cin
    @1
    cA
    cB
    df-res
    cA
    @1
    inss2
    eqsstri
    cB
    cvv
    relxp
    @0
    @1
    relss
    mp2
end
