include "cv.mm"
include "cuni.mm"
include "wpss.mm"
include "wex.mm"
include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "wa.mm"
include "df-pss.mm"
include "wceq.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6req.mm"
include "eqtr.mm"
include "mpdan.mm"
include "necon3i.mm"
include "anim1i.mm"
include "ancoms.mm"
include "sylbi.mm"
include "eximi.mm"
include "cin.mm"
include "crab.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "eqid.mm"
include "vex.mm"
include "inf3lem7.mm"
include "exlimiv.mm"
include "syl.mm"
include "infeq5i.mm"
include "impbii.mm"

theorem infeq5
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w


  assert |- ( E. x x C. U. x <-> _om e. _V )

  proof
    vx
    cv
    #
    @0
    cuni
    #
    wpss
    #
    vx
    wex
    #
    com
    cvv
    wcel
    #
    @3
    @0
    c0
    wne
    #
    @0
    @1
    wss
    #
    wa
    #
    vx
    wex
    @4
    @2
    @7
    vx
    @2
    @6
    @0
    @1
    wne
    #
    wa
    @7
    @0
    @1
    df-pss
    @8
    @6
    @7
    @8
    @5
    @6
    @0
    c0
    @0
    @1
    @0
    c0
    wceq
    #
    c0
    @1
    wceq
    @0
    @1
    wceq
    @9
    @1
    c0
    cuni
    c0
    @0
    c0
    unieq
    uni0
    syl6req
    @0
    c0
    @1
    eqtr
    mpdan
    necon3i
    anim1i
    ancoms
    sylbi
    eximi
    @7
    @4
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
    @10
    @10
    eqid
    @11
    eqid
    vx
    vex
    #
    @12
    inf3lem7
    exlimiv
    syl
    vx
    infeq5i
    impbii
end
