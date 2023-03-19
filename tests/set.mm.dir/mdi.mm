include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "cmd.mm"
include "wbr.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "mdbr.mm"
include "biimpd.mm"
include "sseq1.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylan9.mm"
include "3impa.mm"
include "imp32.mm"

theorem mdi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( A MH B /\ C C_ B ) ) -> ( ( C vH A ) i^i B ) = ( C vH ( A i^i B ) ) )

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
    cmd
    wbr
    #
    cC
    cB
    wss
    #
    cC
    cA
    chj
    co
    #
    cB
    cin
    #
    cC
    cA
    cB
    cin
    #
    chj
    co
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
    vx
    cv
    #
    cB
    wss
    #
    @12
    cA
    chj
    co
    #
    cB
    cin
    #
    @12
    @7
    chj
    co
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
    mdbr
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
    sseq1
    @20
    @15
    @6
    @16
    @8
    @20
    @14
    @5
    cB
    @12
    cC
    cA
    chj
    oveq1
    ineq1d
    @12
    cC
    @7
    chj
    oveq1
    eqeq12d
    imbi12d
    rspcv
    sylan9
    3impa
    imp32
end
