include "cvv.mm"
include "cen.mm"
include "relen.mm"
include "cv.mm"
include "wbr.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "wcel.mm"
include "ccnv.mm"
include "vex.mm"
include "f1ocnv.mm"
include "f1oen2g.mm"
include "mp3an12i.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "f1oco.mm"
include "ancoms.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "enref.mm"
include "2th.mm"
include "iseri.mm"

theorem ener
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ~~ Er _V

  proof
    vx
    vy
    vz
    cvv
    cen
    relen
    vx
    cv
    #
    vy
    cv
    #
    cen
    wbr
    #
    @0
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @1
    @0
    cen
    wbr
    #
    @0
    @1
    vf
    bren
    @4
    @5
    vf
    @1
    cvv
    wcel
    @0
    cvv
    wcel
    #
    @4
    @1
    @0
    @3
    ccnv
    #
    wf1o
    @5
    vy
    vex
    vx
    vex
    #
    @0
    @1
    @3
    f1ocnv
    @1
    @0
    @7
    cvv
    cvv
    f1oen2g
    mp3an12i
    exlimiv
    sylbi
    @2
    @0
    @1
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    @1
    vz
    cv
    #
    @3
    wf1o
    #
    vf
    wex
    #
    @0
    @12
    cen
    wbr
    #
    @1
    @12
    cen
    wbr
    @0
    @1
    vg
    bren
    @1
    @12
    vf
    bren
    @11
    @14
    wa
    @10
    @13
    wa
    #
    vf
    wex
    vg
    wex
    @15
    @10
    @13
    vg
    vf
    eeanv
    @16
    @15
    vg
    vf
    @6
    @12
    cvv
    wcel
    @16
    @0
    @12
    @3
    @9
    ccom
    #
    wf1o
    #
    @15
    @8
    vz
    vex
    @13
    @10
    @18
    @0
    @1
    @12
    @3
    @9
    f1oco
    ancoms
    @0
    @12
    @17
    cvv
    cvv
    f1oen2g
    mp3an12i
    exlimivv
    sylbir
    syl2anb
    @6
    @0
    @0
    cen
    wbr
    @8
    @0
    @8
    enref
    2th
    iseri
end
