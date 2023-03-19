include "cch.mm"
include "wcel.mm"
include "cdmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "dmdbr4.mm"
include "biimpd.mm"
include "wceq.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "oveq1d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "sylan9.mm"
include "3impa.mm"

theorem dmdi4
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( A MH* B -> ( ( C vH B ) i^i ( A vH B ) ) C_ ( ( ( C vH B ) i^i A ) vH B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    cA
    cB
    cdmd
    wbr
    #
    cC
    cB
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    cin
    #
    @4
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    wi
    @0
    @1
    wa
    #
    @3
    vx
    cv
    #
    cB
    chj
    co
    #
    @5
    cin
    #
    @12
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    vx
    cch
    wral
    #
    @2
    @9
    @10
    @3
    @17
    vx
    cA
    cB
    dmdbr4
    biimpd
    @16
    @9
    vx
    cC
    cch
    @11
    cC
    wceq
    #
    @13
    @6
    @15
    @8
    @18
    @12
    @4
    @5
    @11
    cC
    cB
    chj
    oveq1
    #
    ineq1d
    @18
    @14
    @7
    cB
    chj
    @18
    @12
    @4
    cA
    @19
    ineq1d
    oveq1d
    sseq12d
    rspcv
    sylan9
    3impa
end
