include "cps.mm"
include "wcel.mm"
include "crn.mm"
include "csn.mm"
include "cv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "cdm.mm"
include "cordt.mm"
include "eqid.mm"
include "psrn.mm"
include "eqcomd.mm"
include "sneqd.mm"
include "wb.mm"
include "vex.mm"
include "brcnv.mm"
include "a1i.mm"
include "notbid.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "uneq12d.mm"
include "uncom.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "wceq.mm"
include "cnvps.mm"
include "df-rn.mm"
include "ordtval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem ordtcnv
  let cR: class R
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let wph: wff ph
  let cX: class X
  let cV: class V


  assert |- ( R e. PosetRel -> ( ordTop ` `' R ) = ( ordTop ` R ) )

  proof
    cR
    cps
    wcel
    #
    cR
    crn
    #
    csn
    #
    vx
    @1
    vy
    cv
    #
    vx
    cv
    #
    cR
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    @1
    crab
    #
    cmpt
    #
    crn
    #
    vx
    @1
    @4
    @3
    @5
    wbr
    #
    wn
    #
    vy
    @1
    crab
    #
    cmpt
    #
    crn
    #
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    cR
    cdm
    #
    csn
    #
    vx
    @20
    @3
    @4
    cR
    wbr
    #
    wn
    #
    vy
    @20
    crab
    #
    cmpt
    #
    crn
    #
    vx
    @20
    @4
    @3
    cR
    wbr
    #
    wn
    #
    vy
    @20
    crab
    #
    cmpt
    #
    crn
    #
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    @5
    cordt
    cfv
    #
    cR
    cordt
    cfv
    @0
    @18
    @34
    ctg
    @0
    @17
    @33
    cfi
    @0
    @2
    @21
    @16
    @32
    @0
    @1
    @20
    @0
    @20
    @1
    cR
    @20
    @20
    eqid
    #
    psrn
    eqcomd
    #
    sneqd
    @0
    @16
    @31
    @26
    cun
    @32
    @0
    @10
    @31
    @15
    @26
    @0
    @9
    @30
    @0
    vx
    @1
    @8
    @20
    @29
    @37
    @0
    @7
    @28
    vy
    @1
    @20
    @37
    @0
    @6
    @27
    @6
    @27
    wb
    @0
    @3
    @4
    cR
    vy
    vex
    #
    vx
    vex
    #
    brcnv
    a1i
    notbid
    rabeqbidv
    mpteq12dv
    rneqd
    @0
    @14
    @25
    @0
    vx
    @1
    @13
    @20
    @24
    @37
    @0
    @12
    @23
    vy
    @1
    @20
    @37
    @0
    @11
    @22
    @11
    @22
    wb
    @0
    @4
    @3
    cR
    @39
    @38
    brcnv
    a1i
    notbid
    rabeqbidv
    mpteq12dv
    rneqd
    uneq12d
    @31
    @26
    uncom
    syl6eq
    uneq12d
    fveq2d
    fveq2d
    @0
    @5
    cps
    wcel
    @35
    @19
    wceq
    cR
    cnvps
    vx
    vy
    @10
    @15
    @5
    cps
    @1
    cR
    df-rn
    @10
    eqid
    @15
    eqid
    ordtval
    syl
    vx
    vy
    @26
    @31
    cR
    cps
    @20
    @36
    @26
    eqid
    @31
    eqid
    ordtval
    3eqtr4d
end
