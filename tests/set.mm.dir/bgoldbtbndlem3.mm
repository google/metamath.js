include "codd.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "caddc.mm"
include "cmin.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "cico.mm"
include "wa.mm"
include "ceven.mm"
include "wi.mm"
include "cc0.mm"
include "cv.mm"
include "wral.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "breq2d.mm"
include "3anbi123d.mm"
include "rspcv.mm"
include "syl2imc.mm"
include "a1d.mm"
include "3imp.mm"
include "simp2.mm"
include "oddprmALTV.mm"
include "3ad2ant1.mm"
include "anim12i.mm"
include "adantr.mm"
include "omoeALTV.mm"
include "syl.mm"
include "syl5eqel.mm"
include "cr.mm"
include "eldifi.mm"
include "prmz.mm"
include "zred.mm"
include "cfz.mm"
include "fzofzp1.mm"
include "wo.mm"
include "cun.mm"
include "cuz.mm"
include "cz.mm"
include "elfzo2.mm"
include "cle.mm"
include "1zzd.mm"
include "eluz2.mm"
include "zre.mm"
include "leltletr.mm"
include "syl3an.mm"
include "exp5o.mm"
include "com34.mm"
include "sylbi.mm"
include "syl3anbrc.mm"
include "fzisfzounsn.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "cn.mm"
include "c3.mm"
include "eluzge3nn.mm"
include "ad2antrl.mm"
include "ciccp.mm"
include "simplr.mm"
include "iccpartipre.mm"
include "exp31.mm"
include "elsni.mm"
include "wb.mm"
include "mpbird.mm"
include "ex.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "mpd.mm"
include "com12.mm"
include "3impia.mm"
include "cdc.mm"
include "eluzelre.mm"
include "oddz.mm"
include "cxr.mm"
include "rexr.mm"
include "anim12ci.mm"
include "adantl.mm"
include "elico1.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "ltsub1dd.mm"
include "simprr.mm"
include "resubcld.mm"
include "simplll.mm"
include "4re.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "impr.mm"
include "4pos.mm"
include "simpl.mm"
include "ltsubposd.mm"
include "mpbii.mm"
include "simpll.mm"
include "mp2and.mm"
include "exp32.mm"
include "3ad2ant3.mm"
include "com23.mm"
include "syl2an.mm"
include "3adant3.mm"
include "com13.mm"
include "3syl.mm"
include "imp.mm"
include "impcom.mm"
include "adantrr.mm"
include "syl5eqbr.mm"
include "3jca.mm"
include "mpdan.mm"

theorem bgoldbtbndlem3
  let wph: wff ph
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume bgoldbtbnd.m: |- ( ph -> M e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.n: |- ( ph -> N e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.b: |- ( ph -> A. n e. Even ( ( 4 < n /\ n < N ) -> n e. GoldbachEven ) )
  assume bgoldbtbnd.d: |- ( ph -> D e. ( ZZ>= ` 3 ) )
  assume bgoldbtbnd.f: |- ( ph -> F e. ( RePart ` D ) )
  assume bgoldbtbnd.i: |- ( ph -> A. i e. ( 0 ..^ D ) ( ( F ` i ) e. ( Prime \ { 2 } ) /\ ( ( F ` ( i + 1 ) ) - ( F ` i ) ) < ( N - 4 ) /\ 4 < ( ( F ` ( i + 1 ) ) - ( F ` i ) ) ) )
  assume bgoldbtbnd.0: |- ( ph -> ( F ` 0 ) = 7 )
  assume bgoldbtbnd.1: |- ( ph -> ( F ` 1 ) = ; 1 3 )
  assume bgoldbtbnd.l: |- ( ph -> M < ( F ` D ) )
  assume bgoldbtbnd.r: |- ( ph -> ( F ` D ) e. RR )
  assume bgoldbtbndlem3.s: |- S = ( X - ( F ` I ) )

  disjoint D i
  disjoint F i
  disjoint I i
  disjoint N i
  disjoint k x
  assert |- ( ( ph /\ X e. Odd /\ I e. ( 1 ..^ D ) ) -> ( ( X e. ( ( F ` I ) [,) ( F ` ( I + 1 ) ) ) /\ 4 < S ) -> ( S e. Even /\ S < N /\ 4 < S ) ) )

  proof
    wph
    cX
    codd
    wcel
    #
    cI
    c1
    cD
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cI
    cF
    cfv
    #
    cprime
    c2
    csn
    #
    cdif
    #
    wcel
    #
    cI
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @4
    cmin
    co
    #
    cN
    c4
    cmin
    co
    #
    clt
    wbr
    #
    c4
    @10
    clt
    wbr
    #
    w3a
    #
    cX
    @4
    @9
    cico
    co
    wcel
    #
    c4
    cS
    clt
    wbr
    #
    wa
    #
    cS
    ceven
    wcel
    #
    cS
    cN
    clt
    wbr
    #
    @16
    w3a
    #
    wi
    wph
    @0
    @2
    @14
    wph
    @2
    @14
    wi
    @0
    @2
    cI
    cc0
    cD
    cfzo
    co
    #
    wcel
    wph
    vi
    cv
    #
    cF
    cfv
    #
    @6
    wcel
    #
    @22
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @23
    cmin
    co
    #
    @11
    clt
    wbr
    #
    c4
    @27
    clt
    wbr
    #
    w3a
    #
    vi
    @21
    wral
    @14
    @1
    @21
    cI
    cD
    fzo0ss1
    sseli
    bgoldbtbnd.i
    @30
    @14
    vi
    cI
    @21
    @22
    cI
    wceq
    #
    @24
    @7
    @28
    @12
    @29
    @13
    @31
    @23
    @4
    @6
    @22
    cI
    cF
    fveq2
    #
    eleq1d
    @31
    @27
    @10
    @11
    clt
    @31
    @26
    @9
    @23
    @4
    cmin
    @31
    @25
    @8
    cF
    @22
    cI
    c1
    caddc
    oveq1
    fveq2d
    @32
    oveq12d
    #
    breq1d
    @31
    @27
    @10
    c4
    clt
    @33
    breq2d
    3anbi123d
    rspcv
    syl2imc
    a1d
    3imp
    @3
    @14
    wa
    #
    @17
    @20
    @34
    @17
    wa
    #
    @18
    @19
    @16
    @35
    cS
    cX
    @4
    cmin
    co
    #
    ceven
    bgoldbtbndlem3.s
    @35
    @0
    @4
    codd
    wcel
    #
    wa
    #
    @36
    ceven
    wcel
    @34
    @38
    @17
    @3
    @0
    @14
    @37
    wph
    @0
    @2
    simp2
    @7
    @12
    @37
    @13
    @4
    oddprmALTV
    3ad2ant1
    anim12i
    adantr
    cX
    @4
    omoeALTV
    syl
    syl5eqel
    @35
    cS
    @36
    cN
    clt
    bgoldbtbndlem3.s
    @34
    @15
    @36
    cN
    clt
    wbr
    #
    @16
    @34
    @15
    @39
    @14
    @3
    @15
    @39
    wi
    #
    @7
    @12
    @3
    @40
    wi
    #
    @13
    @7
    @12
    @41
    @7
    @4
    cprime
    wcel
    #
    @4
    cr
    wcel
    #
    @12
    @41
    wi
    @4
    cprime
    @5
    eldifi
    @42
    @4
    @4
    prmz
    zred
    @3
    @12
    @43
    @40
    @3
    @9
    cr
    wcel
    #
    @12
    @43
    @40
    wi
    wi
    #
    wph
    @0
    @2
    @44
    @2
    wph
    @0
    wa
    #
    @44
    @2
    @8
    c1
    cD
    cfz
    co
    #
    wcel
    #
    @46
    @44
    wi
    #
    c1
    cD
    cI
    fzofzp1
    @2
    @48
    @8
    @1
    wcel
    #
    @8
    cD
    csn
    #
    wcel
    #
    wo
    #
    @49
    @2
    @48
    @8
    @1
    @51
    cun
    #
    wcel
    @53
    @2
    @47
    @54
    @8
    @2
    cD
    c1
    cuz
    cfv
    #
    wcel
    #
    @47
    @54
    wceq
    @2
    cI
    @55
    wcel
    #
    cD
    cz
    wcel
    #
    cI
    cD
    clt
    wbr
    #
    w3a
    #
    @56
    cI
    c1
    cD
    elfzo2
    @60
    c1
    cz
    wcel
    #
    @58
    c1
    cD
    cle
    wbr
    #
    @56
    @60
    1zzd
    @57
    @58
    @59
    simp2
    @57
    @58
    @59
    @62
    @57
    @61
    cI
    cz
    wcel
    #
    c1
    cI
    cle
    wbr
    #
    w3a
    @58
    @59
    @62
    wi
    #
    wi
    #
    c1
    cI
    eluz2
    @61
    @63
    @64
    @66
    @61
    @63
    @58
    @64
    @65
    @61
    @63
    @58
    @64
    @59
    @62
    @61
    c1
    cr
    wcel
    @63
    cI
    cr
    wcel
    @58
    cD
    cr
    wcel
    @64
    @59
    wa
    @62
    wi
    c1
    zre
    cI
    zre
    cD
    zre
    c1
    cI
    cD
    leltletr
    syl3an
    exp5o
    com34
    3imp
    sylbi
    3imp
    c1
    cD
    eluz2
    syl3anbrc
    sylbi
    c1
    cD
    fzisfzounsn
    syl
    eleq2d
    @8
    @1
    @51
    elun
    syl6bb
    @2
    @50
    @49
    @52
    @2
    @50
    @46
    @44
    @2
    @50
    wa
    #
    @46
    wa
    cF
    @8
    cD
    wph
    cD
    cn
    wcel
    #
    @67
    @0
    wph
    cD
    c3
    cuz
    cfv
    wcel
    @68
    bgoldbtbnd.d
    cD
    eluzge3nn
    syl
    ad2antrl
    wph
    cF
    cD
    ciccp
    cfv
    wcel
    @67
    @0
    bgoldbtbnd.f
    ad2antrl
    @2
    @50
    @46
    simplr
    iccpartipre
    exp31
    @52
    @49
    wi
    @2
    @52
    @8
    cD
    wceq
    #
    @49
    @8
    cD
    elsni
    @69
    @46
    @44
    @69
    @46
    wa
    @44
    cD
    cF
    cfv
    #
    cr
    wcel
    #
    wph
    @71
    @69
    @0
    bgoldbtbnd.r
    ad2antrl
    @69
    @44
    @71
    wb
    @46
    @69
    @9
    @70
    cr
    @8
    cD
    cF
    fveq2
    eleq1d
    adantr
    mpbird
    ex
    syl
    a1i
    jaod
    sylbid
    mpd
    com12
    3impia
    wph
    @0
    @44
    @45
    wi
    #
    @2
    wph
    cN
    cr
    wcel
    #
    cX
    cr
    wcel
    #
    @72
    @0
    wph
    cN
    c1
    c1
    cdc
    #
    cuz
    cfv
    wcel
    @73
    bgoldbtbnd.n
    @75
    cN
    eluzelre
    syl
    @0
    cX
    cX
    oddz
    zred
    @73
    @74
    wa
    #
    @44
    @43
    @12
    @40
    @76
    @44
    @43
    @12
    @40
    wi
    @76
    @44
    @43
    wa
    #
    wa
    #
    @15
    @12
    @39
    @78
    @15
    cX
    cxr
    wcel
    #
    @4
    cX
    cle
    wbr
    #
    cX
    @9
    clt
    wbr
    #
    w3a
    #
    @12
    @39
    wi
    #
    @78
    @4
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    wa
    #
    @15
    @82
    wb
    @77
    @86
    @76
    @44
    @85
    @43
    @84
    @9
    rexr
    @4
    rexr
    anim12ci
    adantl
    @4
    @9
    cX
    elico1
    syl
    @82
    @78
    @83
    @81
    @79
    @78
    @83
    wi
    @80
    @78
    @81
    @83
    @78
    @81
    @12
    @39
    @78
    @81
    @12
    wa
    #
    wa
    @36
    @11
    clt
    wbr
    #
    @11
    cN
    clt
    wbr
    #
    @39
    @78
    @81
    @12
    @88
    @78
    @81
    wa
    #
    @36
    @10
    clt
    wbr
    #
    @12
    @88
    @90
    cX
    @9
    @4
    @73
    @74
    @77
    @81
    simpllr
    @76
    @44
    @43
    @81
    simplrl
    #
    @76
    @44
    @43
    @81
    simplrr
    #
    @78
    @81
    simpr
    ltsub1dd
    @90
    @36
    cr
    wcel
    #
    @10
    cr
    wcel
    @11
    cr
    wcel
    #
    @91
    @12
    wa
    @88
    wi
    @78
    @94
    @81
    @78
    cX
    @4
    @73
    @74
    @77
    simplr
    @76
    @44
    @43
    simprr
    resubcld
    #
    adantr
    @90
    @9
    @4
    @92
    @93
    resubcld
    @90
    cN
    c4
    @73
    @74
    @77
    @81
    simplll
    c4
    cr
    wcel
    #
    @90
    4re
    a1i
    resubcld
    @36
    @10
    @11
    lttr
    syl3anc
    mpand
    impr
    @78
    @89
    @87
    @76
    @89
    @77
    @76
    cc0
    c4
    clt
    wbr
    @89
    4pos
    @76
    c4
    cN
    @97
    @76
    4re
    a1i
    @73
    @74
    simpl
    ltsubposd
    mpbii
    adantr
    adantr
    @78
    @88
    @89
    wa
    @39
    wi
    #
    @87
    @78
    @94
    @95
    @73
    @98
    @96
    @78
    cN
    c4
    @73
    @74
    @77
    simpll
    #
    @97
    @78
    4re
    a1i
    resubcld
    @99
    @36
    @11
    cN
    lttr
    syl3anc
    adantr
    mp2and
    exp32
    com12
    3ad2ant3
    com12
    sylbid
    com23
    exp32
    com34
    syl2an
    3adant3
    mpd
    com13
    3syl
    imp
    3adant3
    impcom
    imp
    adantrr
    syl5eqbr
    @34
    @15
    @16
    simprr
    3jca
    ex
    mpdan
end
