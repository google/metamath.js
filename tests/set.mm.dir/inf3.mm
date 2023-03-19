include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "cin.mm"
include "crab.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "eqid.mm"
include "vex.mm"
include "inf3lem7.mm"
include "exlimiiv.mm"

theorem inf3
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assume inf3.1: |- E. x ( x =/= (/) /\ x C_ U. x )


  assert |- _om e. _V

  proof
    vx
    cv
    #
    c0
    wne
    @0
    @0
    cuni
    wss
    wa
    com
    cvv
    wcel
    vx
    vx
    vy
    vw
    @0
    @0
    vy
    cvv
    vw
    cv
    @0
    cin
    vy
    cv
    wss
    vw
    @0
    crab
    cmpt
    #
    c0
    crdg
    com
    cres
    #
    @1
    @1
    eqid
    @2
    eqid
    vx
    vex
    #
    @3
    inf3lem7
    inf3.1
    exlimiiv
end
