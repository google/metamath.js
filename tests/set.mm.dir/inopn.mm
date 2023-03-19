include "ctop.mm"
include "wcel.mm"
include "cin.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "istopg.mm"
include "ibi.mm"
include "simprd.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ineq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem inopn
  let cA: class A
  let cB: class B
  let cJ: class J
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. Top /\ A e. J /\ B e. J ) -> ( A i^i B ) e. J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wcel
    #
    cB
    cJ
    wcel
    #
    cA
    cB
    cin
    #
    cJ
    wcel
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cJ
    wcel
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    @1
    @2
    wa
    @4
    @0
    @5
    cJ
    wss
    @5
    cuni
    cJ
    wcel
    wi
    vx
    wal
    #
    @9
    @0
    @10
    @9
    wa
    vx
    vy
    ctop
    cJ
    istopg
    ibi
    simprd
    @8
    @4
    cA
    @6
    cin
    #
    cJ
    wcel
    vx
    vy
    cA
    cB
    cJ
    cJ
    @5
    cA
    wceq
    @7
    @11
    cJ
    @5
    cA
    @6
    ineq1
    eleq1d
    @6
    cB
    wceq
    @11
    @3
    cJ
    @6
    cB
    cA
    ineq2
    eleq1d
    rspc2v
    syl5com
    3impib
end
