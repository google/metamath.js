include "wss.mm"
include "cin.mm"
include "cun.mm"
include "wceq.mm"
include "rp-fakeinunass.mm"
include "eqcom.mm"
include "incom.mm"
include "uncom.mm"
include "ineq1i.mm"
include "eqtri.mm"
include "uneq2i.mm"
include "eqeq12i.mm"
include "3bitri.mm"

theorem rp-fakeuninass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ C <-> ( ( A u. B ) i^i C ) = ( A u. ( B i^i C ) ) )

  proof
    cA
    cC
    wss
    cC
    cB
    cin
    #
    cA
    cun
    #
    cC
    cB
    cA
    cun
    #
    cin
    #
    wceq
    @3
    @1
    wceq
    cA
    cB
    cun
    #
    cC
    cin
    #
    cA
    cB
    cC
    cin
    #
    cun
    #
    wceq
    cC
    cB
    cA
    rp-fakeinunass
    @1
    @3
    eqcom
    @3
    @5
    @1
    @7
    @3
    @2
    cC
    cin
    @5
    cC
    @2
    incom
    @2
    @4
    cC
    cB
    cA
    uncom
    ineq1i
    eqtri
    @1
    cA
    @0
    cun
    @7
    @0
    cA
    uncom
    @0
    @6
    cA
    cC
    cB
    incom
    uneq2i
    eqtri
    eqeq12i
    3bitri
end
