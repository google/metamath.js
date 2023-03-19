include "cun.mm"
include "cxp.mm"
include "xpundi.mm"
include "xpundir.mm"
include "uneq12i.mm"
include "un4.mm"
include "3eqtri.mm"

theorem xpun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A u. B ) X. ( C u. D ) ) = ( ( ( A X. C ) u. ( A X. D ) ) u. ( ( B X. C ) u. ( B X. D ) ) )

  proof
    cA
    cB
    cun
    #
    cC
    cD
    cun
    cxp
    @0
    cC
    cxp
    #
    @0
    cD
    cxp
    #
    cun
    cA
    cC
    cxp
    #
    cB
    cC
    cxp
    #
    cun
    #
    cA
    cD
    cxp
    #
    cB
    cD
    cxp
    #
    cun
    #
    cun
    @3
    @6
    cun
    @4
    @7
    cun
    cun
    @0
    cC
    cD
    xpundi
    @1
    @5
    @2
    @8
    cA
    cB
    cC
    xpundir
    cA
    cB
    cD
    xpundir
    uneq12i
    @3
    @4
    @6
    @7
    un4
    3eqtri
end
