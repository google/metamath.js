include "crisc.mm"
include "cdm.mm"
include "wer.mm"
include "wrel.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "crngo.mm"
include "wcel.mm"
include "crngiso.mm"
include "co.mm"
include "wex.mm"
include "df-risc.mm"
include "relopabi.mm"
include "eqid.mm"
include "vex.mm"
include "isrisc.mm"
include "ccnv.mm"
include "rngoisocnv.mm"
include "3expia.mm"
include "risci.mm"
include "ancoms.mm"
include "syld.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylbi.mm"
include "w3a.mm"
include "eeanv.mm"
include "ccom.mm"
include "rngoisoco.mm"
include "ex.mm"
include "3adant2.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "3expb.mm"
include "adantlr.mm"
include "an4s.mm"
include "syl2anb.mm"
include "pm3.2i.mm"
include "ax-gen.mm"
include "gen2.mm"
include "dfer2.mm"
include "mpbir3an.mm"

theorem riscer
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t


  assert |- ~=R Er dom ~=R

  proof
    crisc
    cdm
    #
    crisc
    wer
    crisc
    wrel
    @0
    @0
    wceq
    vr
    cv
    #
    vs
    cv
    #
    crisc
    wbr
    #
    @2
    @1
    crisc
    wbr
    #
    wi
    #
    @3
    @2
    vt
    cv
    #
    crisc
    wbr
    #
    wa
    @1
    @6
    crisc
    wbr
    #
    wi
    #
    wa
    #
    vt
    wal
    #
    vs
    wal
    vr
    wal
    @1
    crngo
    wcel
    #
    @2
    crngo
    wcel
    #
    wa
    #
    vf
    cv
    #
    @1
    @2
    crngiso
    co
    wcel
    #
    vf
    wex
    #
    wa
    #
    vr
    vs
    crisc
    vf
    vs
    vr
    df-risc
    relopabi
    @0
    eqid
    @11
    vr
    vs
    @10
    vt
    @5
    @9
    @3
    @18
    @4
    @1
    @2
    vf
    vr
    vex
    vs
    vex
    #
    isrisc
    #
    @14
    @17
    @4
    @14
    @16
    @4
    vf
    @14
    @16
    @15
    ccnv
    #
    @2
    @1
    crngiso
    co
    wcel
    #
    @4
    @12
    @13
    @16
    @22
    @1
    @2
    @15
    rngoisocnv
    3expia
    @13
    @12
    @22
    @4
    wi
    @13
    @12
    @22
    @4
    @2
    @1
    @21
    risci
    3expia
    ancoms
    syld
    exlimdv
    imp
    sylbi
    @3
    @18
    @13
    @6
    crngo
    wcel
    #
    wa
    #
    vg
    cv
    #
    @2
    @6
    crngiso
    co
    wcel
    #
    vg
    wex
    #
    wa
    @8
    @7
    @20
    @2
    @6
    vg
    @19
    vt
    vex
    isrisc
    @14
    @24
    @17
    @27
    @8
    @14
    @24
    wa
    @17
    @27
    wa
    #
    @8
    @12
    @24
    @28
    @8
    wi
    #
    @13
    @12
    @13
    @23
    @29
    @28
    @16
    @26
    wa
    #
    vg
    wex
    vf
    wex
    @12
    @13
    @23
    w3a
    #
    @8
    @16
    @26
    vf
    vg
    eeanv
    @31
    @30
    @8
    vf
    vg
    @31
    @30
    @25
    @15
    ccom
    #
    @1
    @6
    crngiso
    co
    wcel
    #
    @8
    @31
    @30
    @33
    @1
    @2
    @6
    @15
    @25
    rngoisoco
    ex
    @12
    @23
    @33
    @8
    wi
    @13
    @12
    @23
    @33
    @8
    @1
    @6
    @32
    risci
    3expia
    3adant2
    syld
    exlimdvv
    syl5bir
    3expb
    adantlr
    imp
    an4s
    syl2anb
    pm3.2i
    ax-gen
    gen2
    vr
    vs
    vt
    @0
    crisc
    dfer2
    mpbir3an
end
