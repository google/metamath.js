include "cvv.mm"
include "cen.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "relen.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "wcel.mm"
include "vex.mm"
include "f1oen2g.mm"
include "mp3an12.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "adantl.mm"
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "f1oco.mm"
include "ancoms.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "wb.mm"
include "enref.mm"
include "2th.mm"
include "iserd.mm"
include "trud.mm"

theorem enerOLD
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ~~ Er _V

  proof
    cvv
    cen
    wer
    wtru
    vx
    vy
    vz
    cvv
    cen
    cen
    wrel
    wtru
    relen
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cen
    wbr
    #
    @1
    @0
    cen
    wbr
    #
    wtru
    @2
    @0
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @3
    @0
    @1
    vf
    bren
    @5
    @3
    vf
    @5
    @1
    @0
    @4
    ccnv
    #
    wf1o
    #
    @3
    @0
    @1
    @4
    f1ocnv
    @1
    cvv
    wcel
    @0
    cvv
    wcel
    #
    @7
    @3
    vy
    vex
    vx
    vex
    #
    @1
    @0
    @6
    cvv
    cvv
    f1oen2g
    mp3an12
    syl
    exlimiv
    sylbi
    adantl
    @2
    @1
    vz
    cv
    #
    cen
    wbr
    #
    wa
    @0
    @10
    cen
    wbr
    #
    wtru
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
    @10
    @4
    wf1o
    #
    vf
    wex
    #
    @12
    @11
    @0
    @1
    vg
    bren
    @1
    @10
    vf
    bren
    @15
    @17
    wa
    @14
    @16
    wa
    #
    vf
    wex
    vg
    wex
    @12
    @14
    @16
    vg
    vf
    eeanv
    @18
    @12
    vg
    vf
    @18
    @0
    @10
    @4
    @13
    ccom
    #
    wf1o
    #
    @12
    @16
    @14
    @20
    @0
    @1
    @10
    @4
    @13
    f1oco
    ancoms
    @8
    @10
    cvv
    wcel
    @20
    @12
    @9
    vz
    vex
    @0
    @10
    @19
    cvv
    cvv
    f1oen2g
    mp3an12
    syl
    exlimivv
    sylbir
    syl2anb
    adantl
    @8
    @0
    @0
    cen
    wbr
    #
    wb
    wtru
    @8
    @21
    @9
    @0
    @9
    enref
    2th
    a1i
    iserd
    trud
end
