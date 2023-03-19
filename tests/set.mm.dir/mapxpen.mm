include "wcel.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "ovexd.mm"
include "wf.mm"
include "wral.mm"
include "wa.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "syl.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "cvv.mm"
include "wb.mm"
include "simp1.mm"
include "xpexg.mm"
include "3adant1.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "fovrn.mm"
include "3expa.mm"
include "sylanl1.mm"
include "fmptd.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "ex.mm"
include "ovex.mm"
include "simp3.mm"
include "sylancr.mm"
include "sylibrd.mm"
include "wceq.mm"
include "wfn.mm"
include "elmapfn.mm"
include "ad2antll.mm"
include "fnov.mm"
include "adantlrl.mm"
include "3adant2.mm"
include "simp1l2.mm"
include "simp1l1.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fvmpt2.mm"
include "fveq1d.mm"
include "simp2.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "mpt2eq3dva.mm"
include "eqtr4d.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "a1d.mm"
include "ralrimi.mm"
include "jctil.mm"
include "mpt2eq123.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "ad2antrl.mm"
include "feqmptd.mm"
include "simprl.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "nfmpt22.mm"
include "eqidd.mm"
include "nfmpt21.mm"
include "nfv.mm"
include "fvex.mm"
include "ovmpt4g.mm"
include "mp3an3.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "expcomd.mm"
include "ralrimd.mm"
include "mpteq12.mm"
include "syl6an.mm"
include "impbid.mm"
include "en3d.mm"

theorem mapxpen
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ( A ^m B ) ^m C ) ~~ ( A ^m ( B X. C ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    vf
    vg
    cA
    cB
    cmap
    co
    #
    cC
    cmap
    co
    #
    cA
    cB
    cC
    cxp
    #
    cmap
    co
    #
    vx
    vy
    cB
    cC
    vx
    cv
    #
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    cfv
    #
    cmpt2
    #
    vy
    cC
    vx
    cB
    @8
    @9
    vg
    cv
    #
    co
    #
    cmpt
    #
    cmpt
    #
    @3
    @4
    cC
    cmap
    ovexd
    @3
    cA
    @6
    cmap
    ovexd
    @10
    @5
    wcel
    #
    @13
    @7
    wcel
    #
    @3
    @6
    cA
    @13
    wf
    #
    @18
    @12
    cA
    wcel
    #
    vy
    cC
    wral
    #
    vx
    cB
    wral
    @20
    @18
    @22
    vx
    cB
    @18
    @8
    cB
    wcel
    #
    wa
    @21
    vy
    cC
    @18
    @9
    cC
    wcel
    #
    @23
    @21
    @18
    @24
    wa
    #
    cB
    cA
    @8
    @11
    @25
    @11
    @4
    wcel
    cB
    cA
    @11
    wf
    #
    @18
    cC
    @4
    @9
    @10
    @10
    @4
    cC
    elmapi
    #
    ffvelrnda
    @11
    cA
    cB
    elmapi
    syl
    #
    ffvelrnda
    an32s
    ralrimiva
    ralrimiva
    vx
    vy
    cB
    cC
    @12
    cA
    @13
    @13
    eqid
    #
    fmpt2
    sylib
    @3
    @0
    @6
    cvv
    wcel
    #
    @19
    @20
    wb
    @0
    @1
    @2
    simp1
    @1
    @2
    @30
    @0
    cB
    cC
    cW
    cX
    xpexg
    3adant1
    cA
    @6
    @13
    cV
    cvv
    elmapg
    syl2anc
    syl5ibr
    @3
    @14
    @7
    wcel
    #
    cC
    @4
    @17
    wf
    #
    @17
    @5
    wcel
    #
    @3
    @31
    @32
    @3
    @31
    wa
    #
    vy
    cC
    @16
    @4
    @17
    @34
    @24
    wa
    #
    @16
    @4
    wcel
    #
    cB
    cA
    @16
    wf
    #
    @35
    vx
    cB
    @15
    cA
    @16
    @34
    @6
    cA
    @14
    wf
    #
    @24
    @23
    @15
    cA
    wcel
    #
    @31
    @38
    @3
    @14
    cA
    @6
    elmapi
    adantl
    @38
    @23
    @24
    @39
    @38
    @23
    @24
    @39
    @8
    @9
    cA
    cB
    cC
    @14
    fovrn
    3expa
    an32s
    sylanl1
    @16
    eqid
    #
    fmptd
    #
    @3
    @36
    @37
    wb
    #
    @31
    @24
    @0
    @1
    @42
    @2
    cA
    cB
    @16
    cV
    cW
    elmapg
    3adant3
    ad2antrr
    mpbird
    @17
    eqid
    #
    fmptd
    ex
    @3
    @4
    cvv
    wcel
    @2
    @33
    @32
    wb
    cA
    cB
    cmap
    ovex
    @0
    @1
    @2
    simp3
    @4
    cC
    @17
    cvv
    cX
    elmapg
    sylancr
    sylibrd
    @3
    @18
    @31
    wa
    #
    @10
    @17
    wceq
    #
    @14
    @13
    wceq
    #
    wb
    @3
    @44
    wa
    #
    @45
    @46
    @47
    @46
    @45
    @14
    vx
    vy
    cB
    cC
    @8
    @9
    @17
    cfv
    #
    cfv
    #
    cmpt2
    #
    wceq
    @47
    @14
    vx
    vy
    cB
    cC
    @15
    cmpt2
    #
    @50
    @47
    @14
    @6
    wfn
    #
    @14
    @51
    wceq
    @31
    @52
    @3
    @18
    @14
    cA
    @6
    elmapfn
    ad2antll
    vx
    vy
    cB
    cC
    @14
    fnov
    sylib
    @47
    vx
    vy
    cB
    cC
    @49
    @15
    @47
    @23
    @24
    w3a
    #
    @49
    @8
    @16
    cfv
    #
    @15
    @53
    @8
    @48
    @16
    @53
    @24
    @16
    cvv
    wcel
    #
    @48
    @16
    wceq
    @47
    @23
    @24
    simp3
    @53
    @37
    @1
    @0
    @55
    @47
    @24
    @37
    @23
    @3
    @31
    @24
    @37
    @18
    @41
    adantlrl
    3adant2
    @0
    @1
    @2
    @44
    @23
    @24
    simp1l2
    @0
    @1
    @2
    @44
    @23
    @24
    simp1l1
    cB
    cA
    @16
    cW
    cV
    fex2
    syl3anc
    vy
    cC
    @16
    cvv
    @17
    @43
    fvmpt2
    syl2anc
    fveq1d
    @53
    @23
    @15
    cvv
    wcel
    @54
    @15
    wceq
    @47
    @23
    @24
    simp2
    @8
    @9
    @14
    ovex
    vx
    cB
    @15
    cvv
    @16
    @40
    fvmpt2
    sylancl
    eqtrd
    mpt2eq3dva
    eqtr4d
    @45
    @13
    @50
    @14
    @45
    cB
    cB
    wceq
    #
    cC
    cC
    wceq
    #
    @12
    @49
    wceq
    #
    vy
    cC
    wral
    #
    wa
    #
    vx
    cB
    wral
    @13
    @50
    wceq
    cB
    eqid
    @45
    @60
    vx
    cB
    vx
    @10
    @17
    vx
    vy
    cC
    @16
    vx
    cC
    nfcv
    vx
    cB
    @15
    nfmpt1
    nfmpt
    nfeq2
    @45
    @60
    @23
    @45
    @59
    @57
    @45
    @58
    vy
    cC
    vy
    @10
    @17
    vy
    cC
    @16
    nfmpt1
    nfeq2
    @45
    @58
    @24
    @45
    @8
    @11
    @48
    @9
    @10
    @17
    fveq1
    fveq1d
    a1d
    ralrimi
    cC
    eqid
    #
    jctil
    a1d
    ralrimi
    vx
    vy
    cB
    cC
    @12
    cB
    cC
    @49
    mpt2eq123
    sylancr
    eqeq2d
    syl5ibrcom
    @47
    @45
    @46
    @10
    vy
    cC
    vx
    cB
    @12
    cmpt
    #
    cmpt
    #
    wceq
    @47
    @10
    vy
    cC
    @11
    cmpt
    @63
    @47
    vy
    cC
    @4
    @10
    @18
    cC
    @4
    @10
    wf
    @3
    @31
    @27
    ad2antrl
    feqmptd
    @47
    vy
    cC
    @11
    @62
    @47
    @24
    wa
    vx
    cB
    cA
    @11
    @47
    @18
    @24
    @26
    @3
    @18
    @31
    simprl
    @28
    sylan
    feqmptd
    mpteq2dva
    eqtrd
    @46
    @17
    @63
    @10
    @46
    @57
    @16
    @62
    wceq
    #
    vy
    cC
    wral
    @17
    @63
    wceq
    @61
    @46
    @64
    vy
    cC
    vy
    @14
    @13
    vx
    vy
    cB
    cC
    @12
    nfmpt22
    nfeq2
    @46
    @56
    @24
    @15
    @12
    wceq
    #
    vx
    cB
    wral
    @64
    @46
    cB
    eqidd
    @46
    @24
    @65
    vx
    cB
    vx
    @14
    @13
    vx
    vy
    cB
    cC
    @12
    nfmpt21
    nfeq2
    @24
    vx
    nfv
    @46
    @23
    @24
    @65
    @23
    @24
    wa
    @65
    @46
    @8
    @9
    @13
    co
    #
    @12
    wceq
    #
    @23
    @24
    @12
    cvv
    wcel
    @67
    @8
    @11
    fvex
    vx
    vy
    cB
    cC
    @12
    @13
    cvv
    @29
    ovmpt4g
    mp3an3
    @46
    @15
    @66
    @12
    @8
    @9
    @14
    @13
    oveq
    eqeq1d
    syl5ibr
    expcomd
    ralrimd
    vx
    cB
    @15
    cB
    @12
    mpteq12
    syl6an
    ralrimi
    vy
    cC
    @16
    cC
    @62
    mpteq12
    sylancr
    eqeq2d
    syl5ibrcom
    impbid
    ex
    en3d
end
