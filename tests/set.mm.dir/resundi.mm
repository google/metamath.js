include "cun.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "xpundir.mm"
include "ineq2i.mm"
include "indi.mm"
include "eqtri.mm"
include "df-res.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem resundi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A |` ( B u. C ) ) = ( ( A |` B ) u. ( A |` C ) )

  proof
    cA
    cB
    cC
    cun
    #
    cvv
    cxp
    #
    cin
    #
    cA
    cB
    cvv
    cxp
    #
    cin
    #
    cA
    cC
    cvv
    cxp
    #
    cin
    #
    cun
    #
    cA
    @0
    cres
    cA
    cB
    cres
    #
    cA
    cC
    cres
    #
    cun
    @2
    cA
    @3
    @5
    cun
    #
    cin
    @7
    @1
    @10
    cA
    cB
    cC
    cvv
    xpundir
    ineq2i
    cA
    @3
    @5
    indi
    eqtri
    cA
    @0
    df-res
    @8
    @4
    @9
    @6
    cA
    cB
    df-res
    cA
    cC
    df-res
    uneq12i
    3eqtr4i
end
