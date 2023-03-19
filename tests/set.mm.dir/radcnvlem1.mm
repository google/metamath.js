include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "cc.mm"
include "wceq.mm"
include "pserval2.mm"
include "sylan.mm"
include "cvv.mm"
include "fvexd.mm"
include "psergf.mm"
include "ffvelrnda.mm"
include "serf0.mm"
include "climi0.mm"
include "wa.mm"
include "cdiv.mm"
include "cmpt.mm"
include "simprl.mm"
include "cr.mm"
include "nn0re.mm"
include "adantl.mm"
include "adantr.mm"
include "abscld.mm"
include "wne.mm"
include "0red.mm"
include "absge0d.mm"
include "lelttrd.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "reexpcl.mm"
include "remulcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "wf.mm"
include "recnd.mm"
include "cle.mm"
include "divge0.mm"
include "syl22anc.mm"
include "absidd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "1red.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "geomulcvg.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "eluznn0.mm"
include "ffvelrnd.mm"
include "reexpcld.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "expcld.mm"
include "mulcld.mm"
include "expge0d.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspccva.mm"
include "wi.mm"
include "1re.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "lemul1ad.mm"
include "absmuld.mm"
include "mul32d.mm"
include "absexpd.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "mulid2d.mm"
include "3brtr3d.mm"
include "cz.mm"
include "eluzelz.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "lemuldiv.mm"
include "mpbid.mm"
include "expdivd.mm"
include "3brtr4d.mm"
include "lemul2ad.mm"
include "mulge0d.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "id.mm"
include "fvmpt.mm"
include "syl.mm"
include "cvgcmpce.mm"
include "rexlimddv.mm"

theorem radcnvlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vk: setvar k
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let vr: setvar r
  let cN: class N
  let cR: class R
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume psergf.x: |- ( ph -> X e. CC )
  assume radcnvlem2.y: |- ( ph -> Y e. CC )
  assume radcnvlem2.a: |- ( ph -> ( abs ` X ) < ( abs ` Y ) )
  assume radcnvlem2.c: |- ( ph -> seq 0 ( + , ( G ` Y ) ) e. dom ~~> )
  assume radcnvlem1.h: |- H = ( m e. NN0 |-> ( m x. ( abs ` ( ( G ` X ) ` m ) ) ) )

  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint H m
  disjoint m ph
  disjoint X m
  disjoint G m
  disjoint Y m
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m s
  disjoint m y
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint r s
  disjoint r y
  disjoint G r
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  assert |- ( ph -> seq 0 ( + , H ) e. dom ~~> )

  proof
    wph
    vk
    cv
    #
    cA
    cfv
    #
    cY
    @0
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    caddc
    cH
    cc0
    cseq
    cli
    cdm
    #
    wcel
    vj
    cn0
    wph
    @3
    c1
    vj
    vk
    cY
    cG
    cfv
    #
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    c1
    crp
    wcel
    wph
    1rp
    a1i
    wph
    cY
    cc
    wcel
    #
    @0
    cn0
    wcel
    @0
    @10
    cfv
    @3
    wceq
    radcnvlem2.y
    vx
    cA
    vn
    cG
    @0
    cY
    pser.g
    pserval2
    sylan
    wph
    vk
    @10
    cc0
    cvv
    cn0
    nn0uz
    @11
    wph
    cY
    cG
    fvexd
    radcnvlem2.c
    wph
    cn0
    cc
    @0
    @10
    wph
    vx
    cA
    vn
    cG
    cY
    pser.g
    radcnv.a
    radcnvlem2.y
    psergf
    ffvelrnda
    serf0
    climi0
    wph
    @6
    cn0
    wcel
    #
    @8
    wa
    #
    wa
    #
    c1
    vm
    vi
    cn0
    vi
    cv
    #
    cX
    cabs
    cfv
    #
    cY
    cabs
    cfv
    #
    cdiv
    co
    #
    @16
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cH
    cc0
    @6
    cn0
    nn0uz
    wph
    @13
    @8
    simprl
    #
    @15
    cn0
    cr
    vm
    cv
    #
    @22
    @15
    vi
    cn0
    @21
    cr
    @22
    @15
    @16
    cn0
    wcel
    #
    wa
    @16
    @20
    @25
    @16
    cr
    wcel
    @15
    @16
    nn0re
    adantl
    @15
    @19
    cr
    wcel
    #
    @25
    @20
    cr
    wcel
    @15
    @17
    @18
    @15
    cX
    wph
    cX
    cc
    wcel
    #
    @14
    psergf.x
    adantr
    abscld
    #
    @15
    cY
    wph
    @12
    @14
    radcnvlem2.y
    adantr
    abscld
    #
    wph
    @18
    cc0
    wne
    #
    @14
    wph
    @18
    wph
    cc0
    @17
    @18
    wph
    0red
    wph
    cX
    psergf.x
    abscld
    #
    wph
    cY
    radcnvlem2.y
    abscld
    #
    wph
    cX
    psergf.x
    absge0d
    #
    radcnvlem2.a
    lelttrd
    #
    gt0ne0d
    #
    adantr
    redivcld
    #
    @19
    @16
    reexpcl
    sylan
    remulcld
    @22
    eqid
    #
    fmptd
    ffvelrnda
    @15
    @24
    cn0
    wcel
    #
    wa
    @24
    cH
    cfv
    #
    @15
    cn0
    cr
    @24
    cH
    wph
    cn0
    cr
    cH
    wf
    @14
    wph
    vm
    cn0
    @24
    @24
    cX
    cG
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cr
    cH
    wph
    @38
    wa
    #
    @24
    @42
    @38
    @24
    cr
    wcel
    wph
    @24
    nn0re
    adantl
    @44
    @41
    wph
    cn0
    cc
    @24
    @40
    wph
    vx
    cA
    vn
    cG
    cX
    pser.g
    radcnv.a
    psergf.x
    psergf
    #
    ffvelrnda
    abscld
    remulcld
    radcnvlem1.h
    fmptd
    adantr
    ffvelrnda
    recnd
    wph
    caddc
    @22
    cc0
    cseq
    @9
    wcel
    #
    @14
    wph
    @19
    cc
    wcel
    @19
    cabs
    cfv
    #
    c1
    clt
    wbr
    @46
    wph
    @19
    wph
    @17
    @18
    @31
    @32
    @35
    redivcld
    #
    recnd
    wph
    @47
    @19
    c1
    clt
    wph
    @19
    @48
    wph
    @17
    cr
    wcel
    #
    cc0
    @17
    cle
    wbr
    @18
    cr
    wcel
    #
    cc0
    @18
    clt
    wbr
    #
    cc0
    @19
    cle
    wbr
    @31
    @33
    @32
    @34
    @17
    @18
    divge0
    syl22anc
    absidd
    wph
    @19
    c1
    clt
    wbr
    #
    @17
    @18
    c1
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @17
    @18
    @53
    clt
    radcnvlem2.a
    wph
    @18
    wph
    @18
    @32
    recnd
    mulid1d
    breqtrrd
    wph
    @49
    c1
    cr
    wcel
    #
    @50
    @51
    @52
    @54
    wb
    @31
    wph
    1red
    @32
    @34
    @17
    c1
    @18
    ltdivmul
    syl112anc
    mpbird
    eqbrtrd
    @19
    vi
    @22
    @37
    geomulcvg
    syl2anc
    adantr
    @15
    1red
    @15
    @24
    @7
    wcel
    #
    wa
    #
    @43
    cabs
    cfv
    #
    c1
    @24
    @19
    @24
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @39
    cabs
    cfv
    c1
    @24
    @22
    cfv
    #
    cmul
    co
    cle
    @57
    @43
    @60
    @58
    @61
    cle
    @57
    @42
    @59
    @24
    @57
    @41
    @57
    cn0
    cc
    @24
    @40
    wph
    cn0
    cc
    @40
    wf
    @14
    @56
    @45
    ad2antrr
    @15
    @13
    @56
    @38
    @23
    @24
    @6
    eluznn0
    sylan
    #
    ffvelrnd
    #
    abscld
    #
    @57
    @19
    @24
    @15
    @26
    @56
    @36
    adantr
    @63
    reexpcld
    #
    @57
    @24
    @63
    nn0red
    #
    @57
    @24
    @63
    nn0ge0d
    #
    @57
    @24
    cA
    cfv
    #
    cX
    @24
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @17
    @24
    cexp
    co
    #
    @18
    @24
    cexp
    co
    #
    cdiv
    co
    #
    @42
    @59
    cle
    @57
    @72
    @74
    cmul
    co
    #
    @73
    cle
    wbr
    #
    @72
    @75
    cle
    wbr
    #
    @57
    @69
    cY
    @24
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @73
    cmul
    co
    #
    c1
    @73
    cmul
    co
    @76
    @73
    cle
    @57
    @81
    c1
    @73
    @57
    @80
    @57
    @69
    @79
    @57
    cn0
    cc
    @24
    cA
    wph
    cn0
    cc
    cA
    wf
    @14
    @56
    radcnv.a
    ad2antrr
    @63
    ffvelrnd
    #
    @57
    cY
    @24
    wph
    @12
    @14
    @56
    radcnvlem2.y
    ad2antrr
    #
    @63
    expcld
    #
    mulcld
    #
    abscld
    #
    @57
    1red
    @57
    @17
    @24
    @57
    cX
    wph
    @27
    @14
    @56
    psergf.x
    ad2antrr
    #
    abscld
    #
    @63
    reexpcld
    #
    @57
    @17
    @24
    @89
    @63
    @57
    cX
    @88
    absge0d
    expge0d
    @57
    @81
    c1
    clt
    wbr
    #
    @81
    c1
    cle
    wbr
    #
    @15
    @8
    @56
    @91
    wph
    @13
    @8
    simprr
    @5
    @91
    vk
    @24
    @7
    vk
    vm
    weq
    #
    @4
    @81
    c1
    clt
    @93
    @3
    @80
    cabs
    @93
    @1
    @69
    @2
    @79
    cmul
    @0
    @24
    cA
    fveq2
    @0
    @24
    cY
    cexp
    oveq2
    oveq12d
    fveq2d
    breq1d
    rspccva
    sylan
    @57
    @81
    cr
    wcel
    @55
    @91
    @92
    wi
    @87
    1re
    @81
    c1
    ltle
    sylancl
    mpd
    lemul1ad
    @57
    @71
    @79
    cmul
    co
    #
    cabs
    cfv
    #
    @72
    @79
    cabs
    cfv
    #
    cmul
    co
    @82
    @76
    @57
    @71
    @79
    @57
    @69
    @70
    @83
    @57
    cX
    @24
    @88
    @63
    expcld
    #
    mulcld
    #
    @85
    absmuld
    @57
    @80
    @70
    cmul
    co
    #
    cabs
    cfv
    @81
    @70
    cabs
    cfv
    #
    cmul
    co
    @95
    @82
    @57
    @80
    @70
    @86
    @97
    absmuld
    @57
    @99
    @94
    cabs
    @57
    @69
    @79
    @70
    @83
    @85
    @97
    mul32d
    fveq2d
    @57
    @100
    @73
    @81
    cmul
    @57
    cX
    @24
    @88
    @63
    absexpd
    oveq2d
    3eqtr3d
    @57
    @96
    @74
    @72
    cmul
    @57
    cY
    @24
    @84
    @63
    absexpd
    oveq2d
    3eqtr3d
    @57
    @73
    @57
    @73
    @90
    recnd
    mulid2d
    3brtr3d
    @57
    @72
    cr
    wcel
    @73
    cr
    wcel
    @74
    cr
    wcel
    cc0
    @74
    clt
    wbr
    #
    @77
    @78
    wb
    @57
    @71
    @98
    abscld
    @90
    @57
    @18
    @24
    @15
    @50
    @56
    @29
    adantr
    #
    @63
    reexpcld
    @57
    @50
    @24
    cz
    wcel
    #
    @51
    @101
    @102
    @56
    @103
    @15
    @6
    @24
    eluzelz
    adantl
    wph
    @51
    @14
    @56
    @34
    ad2antrr
    @18
    @24
    expgt0
    syl3anc
    @72
    @73
    @74
    lemuldiv
    syl112anc
    mpbid
    @57
    @41
    @71
    cabs
    @57
    @27
    @38
    @41
    @71
    wceq
    @88
    @63
    vx
    cA
    vn
    cG
    @24
    cX
    pser.g
    pserval2
    syl2anc
    fveq2d
    @57
    @17
    @18
    @24
    @15
    @17
    cc
    wcel
    @56
    @15
    @17
    @28
    recnd
    adantr
    @15
    @18
    cc
    wcel
    @56
    @15
    @18
    @29
    recnd
    adantr
    wph
    @30
    @14
    @56
    @35
    ad2antrr
    @63
    expdivd
    3brtr4d
    lemul2ad
    @57
    @43
    @57
    @24
    @42
    @67
    @65
    remulcld
    @57
    @24
    @42
    @67
    @65
    @68
    @57
    @41
    @64
    absge0d
    mulge0d
    absidd
    @57
    @60
    @57
    @60
    @57
    @24
    @59
    @67
    @66
    remulcld
    recnd
    mulid2d
    3brtr4d
    @57
    @39
    @43
    cabs
    @57
    @38
    @43
    cvv
    wcel
    @39
    @43
    wceq
    @63
    @24
    @42
    cmul
    ovex
    vm
    cn0
    @43
    cvv
    cH
    radcnvlem1.h
    fvmpt2
    sylancl
    fveq2d
    @57
    @62
    @60
    c1
    cmul
    @57
    @38
    @62
    @60
    wceq
    @63
    vi
    @24
    @21
    @60
    cn0
    @22
    vi
    vm
    weq
    #
    @16
    @24
    @20
    @59
    cmul
    @104
    id
    @16
    @24
    @19
    cexp
    oveq2
    oveq12d
    @37
    @24
    @59
    cmul
    ovex
    fvmpt
    syl
    oveq2d
    3brtr4d
    cvgcmpce
    rexlimddv
end
