include "cv.mm"
include "csur.mm"
include "cpw.mm"
include "wcel.mm"
include "csslt.mm"
include "csn.mm"
include "cima.mm"
include "wa.mm"
include "cbday.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "crio.mm"
include "coprab.mm"
include "cdm.mm"
include "wex.mm"
include "copab.mm"
include "cscut.mm"
include "dmoprab.mm"
include "cmpt2.mm"
include "df-scut.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "wtru.mm"
include "wss.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "df-sslt.mm"
include "relopabi.mm"
include "cop.mm"
include "wb.mm"
include "19.42v.mm"
include "ssltss1.mm"
include "vex.mm"
include "elpw.mm"
include "sylibr.mm"
include "pm4.71ri.mm"
include "elimasn.mm"
include "df-br.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "cvv.mm"
include "riotaex.mm"
include "isset.mm"
include "mpbi.mm"
include "biantru.mm"
include "3bitr2i.mm"
include "3bitr2ri.mm"
include "a1i.mm"
include "opabbi2dv.mm"
include "trud.mm"
include "3eqtr4i.mm"

theorem dmscut
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y


  assert |- dom |s = <<s

  proof
    va
    cv
    #
    csur
    cpw
    #
    wcel
    #
    vb
    cv
    #
    csslt
    @0
    csn
    cima
    #
    wcel
    #
    wa
    #
    vc
    cv
    vx
    cv
    #
    cbday
    cfv
    cbday
    @0
    vy
    cv
    #
    csn
    #
    csslt
    wbr
    @9
    @3
    csslt
    wbr
    wa
    vy
    csur
    crab
    #
    cima
    cint
    wceq
    #
    vx
    @10
    crio
    #
    wceq
    #
    wa
    #
    va
    vb
    vc
    coprab
    #
    cdm
    @14
    vc
    wex
    #
    va
    vb
    copab
    #
    cscut
    cdm
    csslt
    @14
    va
    vb
    vc
    dmoprab
    cscut
    @15
    cscut
    va
    vb
    @1
    @4
    @12
    cmpt2
    @15
    vx
    vy
    va
    vb
    df-scut
    va
    vb
    vc
    @1
    @4
    @12
    df-mpt2
    eqtri
    dmeqi
    csslt
    @17
    wceq
    wtru
    @16
    va
    vb
    csslt
    @0
    csur
    wss
    #
    @3
    csur
    wss
    @7
    @8
    cslt
    wbr
    vy
    @3
    wral
    vx
    @0
    wral
    w3a
    va
    vb
    csslt
    vx
    vy
    va
    vb
    df-sslt
    relopabi
    @0
    @3
    cop
    csslt
    wcel
    #
    @16
    wb
    wtru
    @16
    @6
    @13
    vc
    wex
    #
    wa
    #
    @0
    @3
    csslt
    wbr
    #
    @19
    @6
    @13
    vc
    19.42v
    @22
    @2
    @22
    wa
    @6
    @21
    @22
    @2
    @22
    @18
    @2
    @0
    @3
    ssltss1
    @0
    csur
    va
    vex
    #
    elpw
    sylibr
    pm4.71ri
    @5
    @22
    @2
    @5
    @19
    @22
    csslt
    @0
    @3
    @23
    vb
    vex
    elimasn
    @0
    @3
    csslt
    df-br
    #
    bitr4i
    anbi2i
    @20
    @6
    @12
    cvv
    wcel
    @20
    @11
    vx
    @10
    riotaex
    vc
    @12
    isset
    mpbi
    biantru
    3bitr2i
    @24
    3bitr2ri
    a1i
    opabbi2dv
    trud
    3eqtr4i
end
