include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "cado.mm"
include "cdm.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cnlnadj.mm"
include "df-rex.mm"
include "sylib.mm"
include "wf.mm"
include "w3a.mm"
include "inss1.mm"
include "sseli.mm"
include "lnopf.mm"
include "syl.mm"
include "a1d.mm"
include "wi.mm"
include "a1i.mm"
include "adantrd.mm"
include "eqcom.mm"
include "biimpi.mm"
include "2ralimi.mm"
include "wb.mm"
include "adjsym.mm"
include "syl2anr.mm"
include "syl5ib.mm"
include "expimpd.mm"
include "3jcad.mm"
include "copab.mm"
include "dfadj2.mm"
include "eleq2i.mm"
include "vex.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "3anbi13d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "opelopab.mm"
include "bitr2i.mm"
include "syl6ib.mm"
include "eximdv.mm"
include "mpd.mm"
include "eldm2.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem cnlnssadj
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( LinOp i^i ContOp ) C_ dom adjh

  proof
    vy
    clo
    ccop
    cin
    #
    cado
    cdm
    #
    vy
    cv
    #
    @0
    wcel
    #
    @2
    vt
    cv
    #
    cop
    #
    cado
    wcel
    #
    vt
    wex
    #
    @2
    @1
    wcel
    @3
    @4
    @0
    wcel
    #
    vx
    cv
    #
    @2
    cfv
    vz
    cv
    #
    csp
    co
    #
    @9
    @10
    @4
    cfv
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    wa
    #
    vt
    wex
    #
    @7
    @3
    @14
    vt
    @0
    wrex
    @16
    vx
    vz
    vt
    @2
    cnlnadj
    @14
    vt
    @0
    df-rex
    sylib
    @3
    @15
    @6
    vt
    @3
    @15
    chil
    chil
    @2
    wf
    #
    chil
    chil
    @4
    wf
    #
    @9
    @10
    @2
    cfv
    #
    csp
    co
    #
    @9
    @4
    cfv
    #
    @10
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    @6
    @3
    @15
    @17
    @18
    @24
    @3
    @17
    @15
    @3
    @2
    clo
    wcel
    @17
    @0
    clo
    @2
    clo
    ccop
    inss1
    #
    sseli
    @2
    lnopf
    syl
    #
    a1d
    @3
    @8
    @18
    @14
    @8
    @18
    wi
    @3
    @8
    @4
    clo
    wcel
    @18
    @0
    clo
    @4
    @26
    sseli
    @4
    lnopf
    syl
    #
    a1i
    adantrd
    @3
    @8
    @14
    @24
    @14
    @12
    @11
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    @3
    @8
    wa
    @24
    @13
    @29
    vx
    vz
    chil
    chil
    @13
    @29
    @11
    @12
    eqcom
    biimpi
    2ralimi
    @8
    @18
    @17
    @30
    @24
    wb
    @3
    @28
    @27
    vx
    vz
    @4
    @2
    adjsym
    syl2anr
    syl5ib
    expimpd
    3jcad
    @6
    @5
    chil
    chil
    vu
    cv
    #
    wf
    #
    chil
    chil
    vv
    cv
    #
    wf
    #
    @9
    @10
    @31
    cfv
    #
    csp
    co
    #
    @9
    @33
    cfv
    #
    @10
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    vu
    vv
    copab
    #
    wcel
    @25
    cado
    @42
    @5
    vx
    vz
    vv
    vu
    dfadj2
    eleq2i
    @41
    @17
    @34
    @20
    @38
    wceq
    #
    vz
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    @25
    vu
    vv
    @2
    @4
    vy
    vex
    #
    vt
    vex
    @31
    @2
    wceq
    #
    @32
    @17
    @40
    @44
    @34
    chil
    chil
    @31
    @2
    feq1
    @46
    @39
    @43
    vx
    vz
    chil
    chil
    @46
    @36
    @20
    @38
    @46
    @35
    @19
    @9
    csp
    @10
    @31
    @2
    fveq1
    oveq2d
    eqeq1d
    2ralbidv
    3anbi13d
    @33
    @4
    wceq
    #
    @34
    @18
    @44
    @24
    @17
    chil
    chil
    @33
    @4
    feq1
    @47
    @43
    @23
    vx
    vz
    chil
    chil
    @47
    @38
    @22
    @20
    @47
    @37
    @21
    @10
    csp
    @9
    @33
    @4
    fveq1
    oveq1d
    eqeq2d
    2ralbidv
    3anbi23d
    opelopab
    bitr2i
    syl6ib
    eximdv
    mpd
    vt
    @2
    cado
    @45
    eldm2
    sylibr
    ssriv
end
