include "cxp.mm"
include "wf.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "w3a.mm"
include "ccur.mm"
include "cunc.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cfv.mm"
include "wbr.mm"
include "coprab.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "anim1i.mm"
include "3adant3.mm"
include "3anass.mm"
include "curfv.mm"
include "sylanbr.mm"
include "an32s.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "sylan.mm"
include "cmap.mm"
include "curf.mm"
include "ffvelrnda.mm"
include "elmapfn.mm"
include "syl.mm"
include "fnbrfvb.mm"
include "anasss.mm"
include "ibar.mm"
include "adantl.mm"
include "3bitr3d.mm"
include "wn.mm"
include "cdm.mm"
include "cop.mm"
include "df-br.mm"
include "elfvdm.mm"
include "sylbi.mm"
include "fdm.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "sylan2.mm"
include "ffvelrn.mm"
include "elmapi.mm"
include "3syl.mm"
include "vex.mm"
include "breldm.mm"
include "eleq2.mm"
include "syl2an.mm"
include "mpdan.mm"
include "jca.mm"
include "stoic1a.mm"
include "simpl.mm"
include "con3i.mm"
include "2falsed.mm"
include "pm2.61dan.mm"
include "oprabbidv.mm"
include "df-unc.mm"
include "df-mpt2.mm"
include "3eqtr4g.mm"
include "fnov.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "eqtr4d.mm"

theorem unccur
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F : ( A X. B ) --> C /\ B e. ( V \ { (/) } ) /\ C e. W ) -> uncurry curry F = F )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wf
    #
    cB
    cV
    c0
    csn
    cdif
    #
    wcel
    #
    cC
    cW
    wcel
    #
    w3a
    #
    cF
    ccur
    #
    cunc
    #
    vx
    vy
    cA
    cB
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cmpt2
    #
    cF
    @5
    @9
    vz
    cv
    #
    @8
    @6
    cfv
    #
    wbr
    #
    vx
    vy
    vz
    coprab
    @8
    cA
    wcel
    #
    @9
    cB
    wcel
    #
    wa
    #
    @12
    @10
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    @7
    @11
    @5
    @14
    @19
    vx
    vy
    vz
    @5
    @17
    @14
    @19
    wb
    @5
    @17
    wa
    @9
    @13
    cfv
    #
    @12
    wceq
    #
    @18
    @14
    @19
    @5
    cF
    @0
    wfn
    #
    @3
    wa
    #
    @17
    @21
    @18
    wb
    @1
    @3
    @23
    @4
    @1
    @22
    @3
    @0
    cC
    cF
    ffn
    #
    anim1i
    3adant3
    @23
    @17
    wa
    #
    @21
    @10
    @12
    wceq
    @18
    @25
    @20
    @10
    @12
    @22
    @17
    @3
    @20
    @10
    wceq
    #
    @22
    @17
    wa
    @22
    @15
    @16
    w3a
    @3
    @26
    @22
    @15
    @16
    3anass
    @8
    @9
    cF
    cA
    cB
    @2
    curfv
    sylanbr
    an32s
    eqeq1d
    @10
    @12
    eqcom
    syl6bb
    sylan
    @5
    @15
    @16
    @21
    @14
    wb
    #
    @5
    @15
    wa
    #
    @13
    cB
    wfn
    #
    @16
    @27
    @28
    @13
    cC
    cB
    cmap
    co
    #
    wcel
    #
    @29
    @5
    cA
    @30
    @8
    @6
    cA
    cB
    cC
    cF
    cV
    cW
    curf
    #
    ffvelrnda
    @13
    cC
    cB
    elmapfn
    syl
    cB
    @9
    @12
    @13
    fnbrfvb
    sylan
    anasss
    @17
    @18
    @19
    wb
    @5
    @17
    @18
    ibar
    adantl
    3bitr3d
    @5
    @17
    wn
    #
    wa
    @14
    @19
    @5
    @14
    @17
    @5
    cA
    @30
    @6
    wf
    #
    @14
    @17
    @32
    @34
    @14
    wa
    #
    @15
    @16
    @14
    @34
    @8
    @6
    cdm
    #
    wcel
    #
    @15
    @14
    @9
    @12
    cop
    #
    @13
    wcel
    @37
    @9
    @12
    @13
    df-br
    @38
    @8
    @6
    elfvdm
    sylbi
    @34
    @37
    @15
    @34
    @36
    cA
    @8
    cA
    @30
    @6
    fdm
    eleq2d
    biimpa
    sylan2
    #
    @35
    @15
    @16
    @39
    @34
    @15
    @14
    @16
    @34
    @15
    wa
    #
    @13
    cdm
    #
    cB
    wceq
    #
    @9
    @41
    wcel
    #
    @16
    @14
    @40
    @31
    cB
    cC
    @13
    wf
    @42
    cA
    @30
    @8
    @6
    ffvelrn
    @13
    cC
    cB
    elmapi
    cB
    cC
    @13
    fdm
    3syl
    @9
    @12
    @13
    vy
    vex
    vz
    vex
    breldm
    @42
    @43
    @16
    @41
    cB
    @9
    eleq2
    biimpa
    syl2an
    an32s
    mpdan
    jca
    sylan
    stoic1a
    @33
    @19
    wn
    @5
    @19
    @17
    @17
    @18
    simpl
    con3i
    adantl
    2falsed
    pm2.61dan
    oprabbidv
    vx
    vy
    vz
    @6
    df-unc
    vx
    vy
    vz
    cA
    cB
    @10
    df-mpt2
    3eqtr4g
    @1
    @3
    cF
    @11
    wceq
    #
    @4
    @1
    @22
    @44
    @24
    vx
    vy
    cA
    cB
    cF
    fnov
    sylib
    3ad2ant1
    eqtr4d
end
