include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "ct1.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "wa.mm"
include "wceq.mm"
include "ccnv.mm"
include "cima.mm"
include "ccn.mm"
include "co.mm"
include "kqid.mm"
include "ad2antrr.mm"
include "cnima.mm"
include "sylan.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "kqffn.mm"
include "adantr.mm"
include "fnfun.mm"
include "simprl.mm"
include "fndm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "syl2anc.mm"
include "simprr.mm"
include "sylibrd.mm"
include "ralrimdva.mm"
include "cuni.mm"
include "simplr.mm"
include "crn.mm"
include "fnfvelrn.mm"
include "kqtopon.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "t1sep2.mm"
include "syl3anc.mm"
include "syld.mm"
include "w3a.mm"
include "kqfeq.mm"
include "bibi12d.mm"
include "cbvralv.mm"
include "syl6bbr.mm"
include "3expb.mm"
include "adantlr.mm"
include "sylibd.mm"
include "ralrimivva.mm"
include "ex.mm"
include "simpll.mm"
include "kqopn.mm"
include "kqfvima.mm"
include "3expa.mm"
include "an32s.mm"
include "adantllr.mm"
include "crab.mm"
include "kqfval.mm"
include "eqeq12d.mm"
include "rabbi.mm"
include "bitri.mm"
include "biimprd.mm"
include "imim12d.mm"
include "ralimdva.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "eqeq1.mm"
include "ralrn.mm"
include "imbi2d.mm"
include "eqeq2.mm"
include "bitrd.mm"
include "ist1-2.mm"
include "impbid.mm"

theorem isr0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cU: class U
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J o
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint F o
  disjoint F w
  disjoint F z
  disjoint X o
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint m n
  disjoint m o
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n o
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint A o
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m u
  disjoint m v
  disjoint J m
  disjoint n u
  disjoint n v
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( J e. ( TopOn ` X ) -> ( ( KQ ` J ) e. Fre <-> A. z e. X A. w e. X ( A. o e. J ( z e. o -> w e. o ) -> A. o e. J ( z e. o <-> w e. o ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ckq
    cfv
    #
    ct1
    wcel
    #
    vz
    cv
    #
    vo
    cv
    #
    wcel
    #
    vw
    cv
    #
    @5
    wcel
    #
    wi
    #
    vo
    cJ
    wral
    #
    @6
    @8
    wb
    #
    vo
    cJ
    wral
    #
    wi
    #
    vw
    cX
    wral
    #
    vz
    cX
    wral
    #
    @1
    @3
    @15
    @1
    @3
    wa
    #
    @13
    vz
    vw
    cX
    cX
    @16
    @4
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    wa
    #
    wa
    #
    @10
    @4
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    wceq
    #
    @12
    @20
    @10
    @21
    vv
    cv
    #
    wcel
    #
    @22
    @24
    wcel
    #
    wi
    #
    vv
    @2
    wral
    #
    @23
    @20
    @10
    @27
    vv
    @2
    @20
    @24
    @2
    wcel
    #
    wa
    #
    @10
    @4
    cF
    ccnv
    @24
    cima
    #
    wcel
    #
    @7
    @31
    wcel
    #
    wi
    #
    @27
    @30
    @31
    cJ
    wcel
    #
    @10
    @34
    wi
    @20
    cF
    cJ
    @2
    ccn
    co
    wcel
    #
    @29
    @35
    @1
    @36
    @3
    @19
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqid
    ad2antrr
    @24
    cF
    cJ
    @2
    cnima
    sylan
    @9
    @34
    vo
    @31
    cJ
    @5
    @31
    wceq
    @6
    @32
    @8
    @33
    @5
    @31
    @4
    eleq2
    @5
    @31
    @7
    eleq2
    imbi12d
    rspcv
    syl
    @30
    @25
    @32
    @26
    @33
    @30
    cF
    wfun
    #
    @4
    cF
    cdm
    #
    wcel
    @25
    @32
    wb
    @30
    cF
    cX
    wfn
    #
    @37
    @20
    @39
    @29
    @1
    @39
    @3
    @19
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    #
    ad2antrr
    #
    adantr
    #
    cX
    cF
    fnfun
    syl
    #
    @30
    @4
    cX
    @38
    @20
    @17
    @29
    @16
    @17
    @18
    simprl
    #
    adantr
    @30
    @39
    @38
    cX
    wceq
    @42
    cX
    cF
    fndm
    syl
    #
    eleqtrrd
    @4
    @24
    cF
    fvimacnv
    syl2anc
    @30
    @37
    @7
    @38
    wcel
    @26
    @33
    wb
    @43
    @30
    @7
    cX
    @38
    @20
    @18
    @29
    @16
    @17
    @18
    simprr
    #
    adantr
    @45
    eleqtrrd
    @7
    @24
    cF
    fvimacnv
    syl2anc
    imbi12d
    sylibrd
    ralrimdva
    @20
    @3
    @21
    @2
    cuni
    #
    wcel
    @22
    @47
    wcel
    @28
    @23
    wi
    #
    @1
    @3
    @19
    simplr
    @20
    @21
    cF
    crn
    #
    @47
    @20
    @39
    @17
    @21
    @49
    wcel
    @41
    @44
    cX
    @4
    cF
    fnfvelrn
    syl2anc
    @20
    @2
    @49
    ctopon
    cfv
    wcel
    #
    @49
    @47
    wceq
    @1
    @50
    @3
    @19
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    #
    ad2antrr
    @49
    @2
    toponuni
    syl
    #
    eleqtrd
    @20
    @22
    @49
    @47
    @20
    @39
    @18
    @22
    @49
    wcel
    @41
    @46
    cX
    @7
    cF
    fnfvelrn
    syl2anc
    @52
    eleqtrd
    @21
    @22
    vv
    @2
    @47
    @47
    eqid
    t1sep2
    syl3anc
    syld
    @1
    @19
    @23
    @12
    wb
    #
    @3
    @1
    @17
    @18
    @53
    @1
    @17
    @18
    w3a
    @23
    @4
    vy
    cv
    #
    wcel
    #
    @7
    @54
    wcel
    #
    wb
    #
    vy
    cJ
    wral
    #
    @12
    vx
    vy
    @4
    @7
    cF
    cJ
    @0
    cX
    kqval.2
    kqfeq
    @11
    @57
    vo
    vy
    cJ
    @5
    @54
    wceq
    @6
    @55
    @8
    @56
    @5
    @54
    @4
    eleq2
    @5
    @54
    @7
    eleq2
    bibi12d
    cbvralv
    #
    syl6bbr
    3expb
    adantlr
    sylibd
    ralrimivva
    ex
    @1
    @15
    va
    cv
    #
    @24
    wcel
    #
    vb
    cv
    #
    @24
    wcel
    #
    wi
    #
    vv
    @2
    wral
    #
    @60
    @62
    wceq
    #
    wi
    #
    vb
    @49
    wral
    #
    va
    @49
    wral
    #
    @3
    @1
    @15
    @48
    vw
    cX
    wral
    #
    vz
    cX
    wral
    #
    @69
    @1
    @14
    @70
    vz
    cX
    @1
    @17
    wa
    #
    @13
    @48
    vw
    cX
    @72
    @18
    wa
    #
    @28
    @10
    @12
    @23
    @73
    @28
    @9
    vo
    cJ
    @73
    @5
    cJ
    wcel
    #
    wa
    #
    @28
    @21
    cF
    @5
    cima
    #
    wcel
    #
    @22
    @76
    wcel
    #
    wi
    #
    @9
    @75
    @76
    @2
    wcel
    #
    @28
    @79
    wi
    @73
    @1
    @74
    @80
    @1
    @17
    @18
    simpll
    vx
    vy
    @5
    cF
    cJ
    cX
    kqval.2
    kqopn
    sylan
    @27
    @79
    vv
    @76
    @2
    @24
    @76
    wceq
    @25
    @77
    @26
    @78
    @24
    @76
    @21
    eleq2
    @24
    @76
    @22
    eleq2
    imbi12d
    rspcv
    syl
    @75
    @6
    @77
    @8
    @78
    @72
    @74
    @6
    @77
    wb
    #
    @18
    @1
    @74
    @17
    @81
    @1
    @74
    @17
    @81
    vx
    vy
    @4
    @5
    cF
    cJ
    cX
    kqval.2
    kqfvima
    3expa
    an32s
    adantlr
    @1
    @18
    @74
    @8
    @78
    wb
    #
    @17
    @1
    @74
    @18
    @82
    @1
    @74
    @18
    @82
    vx
    vy
    @7
    @5
    cF
    cJ
    cX
    kqval.2
    kqfvima
    3expa
    an32s
    adantllr
    imbi12d
    sylibrd
    ralrimdva
    @73
    @23
    @12
    @73
    @23
    @55
    vy
    cJ
    crab
    #
    @56
    vy
    cJ
    crab
    #
    wceq
    #
    @12
    @73
    @21
    @83
    @22
    @84
    @72
    @21
    @83
    wceq
    @18
    vx
    vy
    @4
    cF
    cJ
    @0
    cX
    kqval.2
    kqfval
    adantr
    @1
    @18
    @22
    @84
    wceq
    @17
    vx
    vy
    @7
    cF
    cJ
    @0
    cX
    kqval.2
    kqfval
    adantlr
    eqeq12d
    @12
    @58
    @85
    @59
    @55
    @56
    vy
    cJ
    rabbi
    bitri
    syl6bbr
    biimprd
    imim12d
    ralimdva
    ralimdva
    @1
    @39
    @69
    @71
    wb
    @40
    @39
    @69
    @25
    @63
    wi
    #
    vv
    @2
    wral
    #
    @21
    @62
    wceq
    #
    wi
    #
    vb
    @49
    wral
    #
    vz
    cX
    wral
    @71
    @68
    @90
    va
    vz
    cX
    cF
    @60
    @21
    wceq
    #
    @67
    @89
    vb
    @49
    @91
    @65
    @87
    @66
    @88
    @91
    @64
    @86
    vv
    @2
    @91
    @61
    @25
    @63
    @60
    @21
    @24
    eleq1
    imbi1d
    ralbidv
    @60
    @21
    @62
    eqeq1
    imbi12d
    ralbidv
    ralrn
    @39
    @90
    @70
    vz
    cX
    @89
    @48
    vb
    vw
    cX
    cF
    @62
    @22
    wceq
    #
    @87
    @28
    @88
    @23
    @92
    @86
    @27
    vv
    @2
    @92
    @63
    @26
    @25
    @62
    @22
    @24
    eleq1
    imbi2d
    ralbidv
    @62
    @22
    @21
    eqeq2
    imbi12d
    ralrn
    ralbidv
    bitrd
    syl
    sylibrd
    @1
    @50
    @3
    @69
    wb
    @51
    va
    vb
    vv
    @2
    @49
    ist1-2
    syl
    sylibrd
    impbid
end
