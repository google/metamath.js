include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "inss1.mm"
include "eqsstri.mm"

theorem resss
  let cA: class A
  let cB: class B


  assert |- ( A |` B ) C_ A

  proof
    cA
    cB
    cres
    cA
    cB
    cvv
    cxp
    #
    cin
    cA
    cA
    cB
    df-res
    cA
    @0
    inss1
    eqsstri
end
