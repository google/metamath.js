include "cbigcup.mm"
include "cvv.mm"
include "cv.mm"
include "cuni.mm"
include "cmpt.mm"
include "relbigcup.mm"
include "mptrel.mm"
include "wceq.mm"
include "wbr.mm"
include "eqcom.mm"
include "vex.mm"
include "brbigcup.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "eleq1.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "eqeq1.mm"
include "df-mpt.mm"
include "brab.mm"
include "3bitr4i.mm"
include "eqbrriv.mm"

theorem dfbigcup2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t


  assert |- Bigcup = ( x e. _V |-> U. x )

  proof
    vy
    vz
    cbigcup
    vx
    cvv
    vx
    cv
    #
    cuni
    #
    cmpt
    #
    relbigcup
    vx
    cvv
    @1
    mptrel
    vy
    cv
    #
    cuni
    #
    vz
    cv
    #
    wceq
    @5
    @4
    wceq
    #
    @3
    @5
    cbigcup
    wbr
    @3
    @5
    @2
    wbr
    @4
    @5
    eqcom
    @3
    @5
    vz
    vex
    #
    brbigcup
    @0
    cvv
    wcel
    #
    vt
    cv
    #
    @1
    wceq
    #
    wa
    #
    @9
    @4
    wceq
    #
    @6
    vx
    vt
    @3
    @5
    @2
    vy
    vex
    #
    @7
    vx
    vy
    weq
    #
    @11
    @3
    cvv
    wcel
    #
    @12
    wa
    @12
    @14
    @8
    @15
    @10
    @12
    @0
    @3
    cvv
    eleq1
    @14
    @1
    @4
    @9
    @0
    @3
    unieq
    eqeq2d
    anbi12d
    @15
    @12
    @13
    biantrur
    syl6bbr
    @9
    @5
    @4
    eqeq1
    vx
    vt
    cvv
    @1
    df-mpt
    brab
    3bitr4i
    eqbrriv
end
