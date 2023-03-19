include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "ccm.mm"
include "wbr.mm"
include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "id.mm"
include "ineq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "ineq2.mm"
include "fveq2.mm"
include "ineq2d.mm"
include "eqeq2d.mm"
include "df-cm.mm"
include "brabg.mm"
include "bianabs.mm"

theorem cmbr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_H B <-> A = ( ( A i^i B ) vH ( A i^i ( _|_ ` B ) ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cB
    ccm
    wbr
    cA
    cA
    cB
    cin
    #
    cA
    cB
    cort
    cfv
    #
    cin
    #
    chj
    co
    #
    wceq
    #
    vx
    cv
    #
    cch
    wcel
    #
    vy
    cv
    #
    cch
    wcel
    #
    wa
    #
    @8
    @8
    @10
    cin
    #
    @8
    @10
    cort
    cfv
    #
    cin
    #
    chj
    co
    #
    wceq
    #
    wa
    @0
    @11
    wa
    #
    cA
    cA
    @10
    cin
    #
    cA
    @14
    cin
    #
    chj
    co
    #
    wceq
    #
    wa
    @2
    @7
    wa
    vx
    vy
    cA
    cB
    cch
    cch
    ccm
    @8
    cA
    wceq
    #
    @12
    @18
    @17
    @22
    @23
    @9
    @0
    @11
    @8
    cA
    cch
    eleq1
    anbi1d
    @23
    @8
    cA
    @16
    @21
    @23
    id
    @23
    @13
    @19
    @15
    @20
    chj
    @8
    cA
    @10
    ineq1
    @8
    cA
    @14
    ineq1
    oveq12d
    eqeq12d
    anbi12d
    @10
    cB
    wceq
    #
    @18
    @2
    @22
    @7
    @24
    @11
    @1
    @0
    @10
    cB
    cch
    eleq1
    anbi2d
    @24
    @21
    @6
    cA
    @24
    @19
    @3
    @20
    @5
    chj
    @10
    cB
    cA
    ineq2
    @24
    @14
    @4
    cA
    @10
    cB
    cort
    fveq2
    ineq2d
    oveq12d
    eqeq2d
    anbi12d
    vx
    vy
    df-cm
    brabg
    bianabs
end
