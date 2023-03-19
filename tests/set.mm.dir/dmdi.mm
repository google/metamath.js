include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "cdmd.mm"
include "wbr.mm"
include "wss.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "dmdbr.mm"
include "biimpd.mm"
include "sseq2.mm"
include "ineq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylan9.mm"
include "3impa.mm"
include "imp32.mm"

theorem dmdi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( A MH* B /\ B C_ C ) ) -> ( ( C i^i A ) vH B ) = ( C i^i ( A vH B ) ) )

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
    w3a
    cA
    cB
    cdmd
    wbr
    #
    cB
    cC
    wss
    #
    cC
    cA
    cin
    #
    cB
    chj
    co
    #
    cC
    cA
    cB
    chj
    co
    #
    cin
    #
    wceq
    #
    @0
    @1
    @2
    @3
    @4
    @9
    wi
    #
    wi
    @0
    @1
    wa
    #
    @3
    cB
    vx
    cv
    #
    wss
    #
    @12
    cA
    cin
    #
    cB
    chj
    co
    #
    @12
    @7
    cin
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    #
    @2
    @10
    @11
    @3
    @19
    vx
    cA
    cB
    dmdbr
    biimpd
    @18
    @10
    vx
    cC
    cch
    @12
    cC
    wceq
    #
    @13
    @4
    @17
    @9
    @12
    cC
    cB
    sseq2
    @20
    @15
    @6
    @16
    @8
    @20
    @14
    @5
    cB
    chj
    @12
    cC
    cA
    ineq1
    oveq1d
    @12
    cC
    @7
    ineq1
    eqeq12d
    imbi12d
    rspcv
    sylan9
    3impa
    imp32
end
