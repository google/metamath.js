include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "simp1.mm"
include "elfvex.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "simp2.mm"
include "csn.mm"
include "cxp.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "simpll3.mm"
include "simpll2.mm"
include "wf.mm"
include "mzpf.mm"
include "ffvelrnda.mm"
include "expcom.mm"
include "ralimdv.mm"
include "imp.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "adantr.mm"
include "wb.mm"
include "zex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "syl21anc.mm"
include "vex.mm"
include "fvconst2.mm"
include "syl.mm"
include "mpteq2dva.mm"
include "mzpconstmpt.mm"
include "3ad2antl1.mm"
include "eqeltrd.mm"
include "csb.mm"
include "fveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "simplr.mm"
include "csbeq1.mm"
include "fveq1d.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "simpl3.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "feqmptd.mm"
include "eqtr4d.mm"
include "wfn.mm"
include "simp2l.mm"
include "ffn.mm"
include "simp3l.mm"
include "simp13.mm"
include "simp12.mm"
include "simplll.mm"
include "simpllr.mm"
include "ovexd.mm"
include "simplrl.mm"
include "simplrr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "simp2r.mm"
include "simp3r.mm"
include "mzpaddmpt.mm"
include "syl2anc.mm"
include "mzpmulmpt.mm"
include "mpteq2dv.mm"
include "mzpindd.mm"
include "syl31anc.mm"

theorem mzpsubst
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint W x
  disjoint W y
  disjoint x y
  disjoint F x
  disjoint V x
  disjoint V y
  disjoint G x
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint G a
  disjoint G b
  disjoint G c
  assert |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ A. y e. V G e. ( mzPoly ` W ) ) -> ( x e. ( ZZ ^m W ) |-> ( F ` ( y e. V |-> ( G ` x ) ) ) ) e. ( mzPoly ` W ) )

  proof
    cW
    cvv
    wcel
    #
    cF
    cV
    cmzp
    cfv
    wcel
    #
    cG
    cW
    cmzp
    cfv
    #
    wcel
    #
    vy
    cV
    wral
    #
    w3a
    @0
    cV
    cvv
    wcel
    #
    @4
    @1
    vx
    cz
    cW
    cmap
    co
    #
    vy
    cV
    vx
    cv
    #
    cG
    cfv
    #
    cmpt
    #
    cF
    cfv
    #
    cmpt
    #
    @2
    wcel
    #
    @0
    @1
    @4
    simp1
    @1
    @0
    @5
    @4
    cF
    cV
    cmzp
    elfvex
    3ad2ant2
    @0
    @1
    @4
    simp3
    @0
    @1
    @4
    simp2
    @0
    @5
    @4
    w3a
    #
    vx
    @6
    @9
    va
    cv
    #
    cfv
    #
    cmpt
    #
    @2
    wcel
    vx
    @6
    @9
    cz
    cV
    cmap
    co
    #
    vb
    cv
    #
    csn
    cxp
    #
    cfv
    #
    cmpt
    #
    @2
    wcel
    vx
    @6
    @9
    vc
    @17
    @18
    vc
    cv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    @2
    wcel
    vx
    @6
    @9
    @18
    cfv
    #
    cmpt
    #
    @2
    wcel
    #
    vx
    @6
    @9
    @22
    cfv
    #
    cmpt
    #
    @2
    wcel
    #
    vx
    @6
    @9
    @18
    @22
    caddc
    cof
    co
    #
    cfv
    #
    cmpt
    #
    @2
    wcel
    vx
    @6
    @9
    @18
    @22
    cmul
    cof
    co
    #
    cfv
    #
    cmpt
    #
    @2
    wcel
    @12
    va
    cF
    vb
    vc
    cV
    @13
    @18
    cz
    wcel
    #
    wa
    #
    @21
    vx
    @6
    @18
    cmpt
    #
    @2
    @40
    vx
    @6
    @20
    @18
    @40
    @7
    @6
    wcel
    #
    wa
    #
    @9
    @17
    wcel
    #
    @20
    @18
    wceq
    @43
    @42
    @4
    @5
    @44
    @40
    @42
    simpr
    @0
    @5
    @4
    @39
    @42
    simpll3
    @0
    @5
    @4
    @39
    @42
    simpll2
    @42
    @4
    wa
    #
    @5
    wa
    #
    @44
    cV
    cz
    @9
    wf
    #
    @45
    @47
    @5
    @45
    @8
    cz
    wcel
    #
    vy
    cV
    wral
    #
    @47
    @42
    @4
    @49
    @42
    @3
    @48
    vy
    cV
    @3
    @42
    @48
    @3
    @6
    cz
    @7
    cG
    cG
    cW
    mzpf
    ffvelrnda
    expcom
    ralimdv
    #
    imp
    vy
    cV
    cz
    @8
    @9
    @9
    eqid
    fmpt
    #
    sylib
    adantr
    @46
    cz
    cvv
    wcel
    #
    @5
    @44
    @47
    wb
    #
    zex
    @45
    @5
    simpr
    cz
    cV
    @9
    cvv
    cvv
    elmapg
    #
    sylancr
    mpbird
    #
    syl21anc
    @17
    @18
    @9
    vb
    vex
    fvconst2
    syl
    mpteq2dva
    @0
    @5
    @39
    @41
    @2
    wcel
    @4
    vx
    @18
    cW
    mzpconstmpt
    3ad2antl1
    eqeltrd
    @13
    @18
    cV
    wcel
    #
    wa
    #
    @26
    vy
    @18
    cG
    csb
    #
    @2
    @57
    @26
    vx
    @6
    @7
    @58
    cfv
    #
    cmpt
    @58
    @57
    vx
    @6
    @25
    @59
    @57
    @42
    wa
    #
    @25
    @18
    @9
    cfv
    #
    @59
    @60
    @44
    @25
    @61
    wceq
    @60
    @42
    @4
    @5
    @44
    @57
    @42
    simpr
    @0
    @5
    @4
    @56
    @42
    simpll3
    @0
    @5
    @4
    @56
    @42
    simpll2
    @55
    syl21anc
    vc
    @9
    @23
    @61
    @17
    @24
    @18
    @22
    @9
    fveq1
    @24
    eqid
    @18
    @9
    fvex
    fvmpt
    syl
    @60
    @56
    @59
    cvv
    wcel
    @61
    @59
    wceq
    @13
    @56
    @42
    simplr
    @7
    @58
    fvex
    va
    @18
    @7
    vy
    @14
    cG
    csb
    #
    cfv
    #
    @59
    cV
    cvv
    @9
    @14
    @18
    wceq
    #
    @7
    @62
    @58
    vy
    @14
    @18
    cG
    csbeq1
    fveq1d
    vy
    va
    cV
    @8
    @63
    va
    @8
    nfcv
    vy
    @7
    @62
    vy
    @14
    cG
    nfcsb1v
    vy
    @7
    nfcv
    nffv
    vy
    cv
    #
    @14
    wceq
    @7
    cG
    @62
    vy
    @14
    cG
    csbeq1a
    fveq1d
    cbvmpt
    fvmptg
    sylancl
    eqtrd
    mpteq2dva
    @57
    vx
    @6
    cz
    @58
    @57
    @58
    @2
    wcel
    #
    @6
    cz
    @58
    wf
    @57
    @56
    @4
    @66
    @13
    @56
    simpr
    @0
    @5
    @4
    @56
    simpl3
    @3
    @66
    vy
    @18
    cV
    vy
    @58
    @2
    vy
    @18
    cG
    nfcsb1v
    nfel1
    @65
    @18
    wceq
    cG
    @58
    @2
    vy
    @18
    cG
    csbeq1a
    eleq1d
    rspc
    sylc
    #
    @58
    cW
    mzpf
    syl
    feqmptd
    eqtr4d
    @67
    eqeltrd
    @13
    @17
    cz
    @18
    wf
    #
    @29
    wa
    #
    @17
    cz
    @22
    wf
    #
    @32
    wa
    #
    w3a
    #
    @35
    vx
    @6
    @27
    @30
    caddc
    co
    #
    cmpt
    #
    @2
    @72
    @18
    @17
    wfn
    #
    @22
    @17
    wfn
    #
    @4
    @5
    @35
    @74
    wceq
    @72
    @68
    @75
    @13
    @68
    @29
    @71
    simp2l
    @17
    cz
    @18
    ffn
    syl
    #
    @72
    @70
    @76
    @13
    @69
    @70
    @32
    simp3l
    @17
    cz
    @22
    ffn
    syl
    #
    @0
    @5
    @4
    @69
    @71
    simp13
    #
    @0
    @5
    @4
    @69
    @71
    simp12
    #
    @75
    @76
    wa
    #
    @4
    @5
    wa
    #
    wa
    #
    vx
    @6
    @34
    @73
    @83
    @42
    wa
    #
    @75
    @76
    @17
    cvv
    wcel
    #
    @44
    @34
    @73
    wceq
    @75
    @76
    @82
    @42
    simplll
    #
    @75
    @76
    @82
    @42
    simpllr
    #
    @84
    cz
    cV
    cmap
    ovexd
    #
    @84
    @44
    @47
    @84
    @49
    @47
    @84
    @42
    @4
    @49
    @83
    @42
    simpr
    @81
    @4
    @5
    @42
    simplrl
    @50
    sylc
    @51
    sylib
    @84
    @52
    @5
    @53
    zex
    @81
    @4
    @5
    @42
    simplrr
    @54
    sylancr
    mpbird
    #
    @17
    caddc
    @18
    @22
    cvv
    @9
    fnfvof
    syl22anc
    mpteq2dva
    syl22anc
    @72
    @29
    @32
    @74
    @2
    wcel
    @13
    @68
    @29
    @71
    simp2r
    #
    @13
    @69
    @70
    @32
    simp3r
    #
    vx
    @27
    @30
    cW
    mzpaddmpt
    syl2anc
    eqeltrd
    @72
    @38
    vx
    @6
    @27
    @30
    cmul
    co
    #
    cmpt
    #
    @2
    @72
    @75
    @76
    @4
    @5
    @38
    @93
    wceq
    @77
    @78
    @79
    @80
    @83
    vx
    @6
    @37
    @92
    @84
    @75
    @76
    @85
    @44
    @37
    @92
    wceq
    @86
    @87
    @88
    @89
    @17
    cmul
    @18
    @22
    cvv
    @9
    fnfvof
    syl22anc
    mpteq2dva
    syl22anc
    @72
    @29
    @32
    @93
    @2
    wcel
    @90
    @91
    vx
    @27
    @30
    cW
    mzpmulmpt
    syl2anc
    eqeltrd
    @14
    @19
    wceq
    #
    @16
    @21
    @2
    @94
    vx
    @6
    @15
    @20
    @9
    @14
    @19
    fveq1
    mpteq2dv
    eleq1d
    @14
    @24
    wceq
    #
    @16
    @26
    @2
    @95
    vx
    @6
    @15
    @25
    @9
    @14
    @24
    fveq1
    mpteq2dv
    eleq1d
    @64
    @16
    @28
    @2
    @64
    vx
    @6
    @15
    @27
    @9
    @14
    @18
    fveq1
    mpteq2dv
    eleq1d
    @14
    @22
    wceq
    #
    @16
    @31
    @2
    @96
    vx
    @6
    @15
    @30
    @9
    @14
    @22
    fveq1
    mpteq2dv
    eleq1d
    @14
    @33
    wceq
    #
    @16
    @35
    @2
    @97
    vx
    @6
    @15
    @34
    @9
    @14
    @33
    fveq1
    mpteq2dv
    eleq1d
    @14
    @36
    wceq
    #
    @16
    @38
    @2
    @98
    vx
    @6
    @15
    @37
    @9
    @14
    @36
    fveq1
    mpteq2dv
    eleq1d
    @14
    cF
    wceq
    #
    @16
    @11
    @2
    @99
    vx
    @6
    @15
    @10
    @9
    @14
    cF
    fveq1
    mpteq2dv
    eleq1d
    mzpindd
    syl31anc
end
