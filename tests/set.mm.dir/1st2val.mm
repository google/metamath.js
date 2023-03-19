include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "weq.mm"
include "coprab.mm"
include "cfv.mm"
include "c1st.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "elvv.mm"
include "fveq2.mm"
include "co.mm"
include "df-ov.mm"
include "vex.mm"
include "simpl.mm"
include "cmpt2.mm"
include "mpt2v.mm"
include "eqcomi.mm"
include "ovmpt2a.mm"
include "mp2an.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "op1std.mm"
include "eqtr4d.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "wn.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "c0.mm"
include "wa.mm"
include "copab.mm"
include "pm3.2i.mm"
include "ax6ev.mm"
include "2th.mm"
include "opabbii.mm"
include "df-xp.mm"
include "dmoprab.mm"
include "3eqtr4ri.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "wne.mm"
include "dmsnn0.mm"
include "biimpri.mm"
include "necon1bi.mm"
include "unieqd.mm"
include "uni0.mm"
include "1stval.mm"
include "syl6eqr.mm"
include "pm2.61i.mm"

theorem 1st2val
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint v x
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint A v
  disjoint A w
  assert |- ( { <. <. x , y >. , z >. | z = x } ` A ) = ( 1st ` A )

  proof
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cA
    vz
    vx
    weq
    #
    vx
    vy
    vz
    coprab
    #
    cfv
    #
    cA
    c1st
    cfv
    #
    wceq
    #
    @1
    cA
    vw
    cv
    #
    vv
    cv
    #
    cop
    #
    wceq
    #
    vv
    wex
    vw
    wex
    @6
    vw
    vv
    cA
    elvv
    @10
    @6
    vw
    vv
    @10
    @4
    @7
    @5
    @10
    @4
    @9
    @3
    cfv
    #
    @7
    cA
    @9
    @3
    fveq2
    @7
    @8
    @3
    co
    #
    @11
    @7
    @7
    @8
    @3
    df-ov
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @12
    @7
    wceq
    vw
    vex
    #
    vv
    vex
    #
    vx
    vy
    @7
    @8
    cvv
    cvv
    vx
    cv
    #
    @7
    @3
    vx
    vw
    weq
    vy
    vv
    weq
    simpl
    vx
    vy
    cvv
    cvv
    @15
    cmpt2
    @3
    vx
    vy
    vz
    @15
    mpt2v
    eqcomi
    @13
    ovmpt2a
    mp2an
    eqtr3i
    syl6eq
    @7
    @8
    cA
    @13
    @14
    op1std
    eqtr4d
    exlimivv
    sylbi
    @1
    wn
    #
    @4
    cA
    csn
    cdm
    #
    cuni
    #
    @5
    @16
    @4
    c0
    @18
    @1
    cA
    @3
    cdm
    #
    wcel
    @4
    c0
    wceq
    @19
    @0
    cA
    @15
    cvv
    wcel
    #
    vy
    cv
    cvv
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @2
    vz
    wex
    #
    vx
    vy
    copab
    @0
    @19
    @22
    @23
    vx
    vy
    @22
    @23
    @20
    @21
    vx
    vex
    vy
    vex
    pm3.2i
    vz
    vx
    ax6ev
    2th
    opabbii
    vx
    vy
    cvv
    cvv
    df-xp
    @2
    vx
    vy
    vz
    dmoprab
    3eqtr4ri
    eleq2i
    cA
    @3
    ndmfv
    sylnbir
    @16
    @18
    c0
    cuni
    c0
    @16
    @17
    c0
    @1
    @17
    c0
    @1
    @17
    c0
    wne
    cA
    dmsnn0
    biimpri
    necon1bi
    unieqd
    uni0
    syl6eq
    eqtr4d
    cA
    1stval
    syl6eqr
    pm2.61i
end
