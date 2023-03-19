include "com.mm"
include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wss.mm"
include "0ex.mm"
include "elintab.mm"
include "simpl.mm"
include "mpgbir.mm"
include "wal.mm"
include "wceq.mm"
include "suceq.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "adantl.mm"
include "a2i.mm"
include "alimi.mm"
include "vex.mm"
include "sucex.mm"
include "3imtr4i.mm"
include "rgenw.mm"
include "peano5.mm"
include "mp2an.mm"
include "peano1.mm"
include "peano2.mm"
include "rgen.mm"
include "omex.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylbi.mm"
include "mp2ani.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem dfom3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- _om = |^| { x | ( (/) e. x /\ A. y e. x suc y e. x ) }

  proof
    com
    c0
    vx
    cv
    #
    wcel
    #
    vy
    cv
    #
    csuc
    #
    @0
    wcel
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    cab
    cint
    #
    c0
    @7
    wcel
    #
    vz
    cv
    #
    @7
    wcel
    #
    @9
    csuc
    #
    @7
    wcel
    #
    wi
    #
    vz
    com
    wral
    com
    @7
    wss
    @8
    @6
    @1
    wi
    vx
    @6
    vx
    c0
    0ex
    elintab
    @1
    @5
    simpl
    mpgbir
    @13
    vz
    com
    @6
    @9
    @0
    wcel
    #
    wi
    #
    vx
    wal
    #
    @6
    @11
    @0
    wcel
    #
    wi
    #
    vx
    wal
    @10
    @12
    @15
    @18
    vx
    @6
    @14
    @17
    @5
    @14
    @17
    wi
    @1
    @4
    @17
    vy
    @9
    @0
    @2
    @9
    wceq
    @3
    @11
    @0
    @2
    @9
    suceq
    eleq1d
    rspccv
    adantl
    a2i
    alimi
    @6
    vx
    @9
    vz
    vex
    #
    elintab
    #
    @6
    vx
    @11
    @9
    @19
    sucex
    elintab
    3imtr4i
    rgenw
    vz
    @7
    peano5
    mp2an
    vz
    @7
    com
    @10
    c0
    com
    wcel
    #
    @3
    com
    wcel
    #
    vy
    com
    wral
    #
    @9
    com
    wcel
    #
    peano1
    @22
    vy
    com
    @2
    peano2
    rgen
    @10
    @16
    @21
    @23
    wa
    #
    @24
    wi
    #
    @20
    @15
    @26
    vx
    com
    omex
    @0
    com
    wceq
    #
    @6
    @25
    @14
    @24
    @27
    @1
    @21
    @5
    @23
    @0
    com
    c0
    eleq2
    @4
    @22
    vy
    @0
    com
    @0
    com
    @3
    eleq2
    raleqbi1dv
    anbi12d
    @0
    com
    @9
    eleq2
    imbi12d
    spcv
    sylbi
    mp2ani
    ssriv
    eqssi
end
