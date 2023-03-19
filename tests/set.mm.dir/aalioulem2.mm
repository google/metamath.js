include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "cz.mm"
include "crp.mm"
include "wrex.mm"
include "cexp.mm"
include "cr.mm"
include "c1.mm"
include "csn.mm"
include "ccnv.mm"
include "cima.mm"
include "crab.mm"
include "cun.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "wss.mm"
include "1rp.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssrab2.mm"
include "unssi.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "ltso.mm"
include "a1i.mm"
include "snfi.mm"
include "cab.mm"
include "chash.mm"
include "cdgr.mm"
include "cply.mm"
include "c0p.mm"
include "wa.mm"
include "nnne0d.mm"
include "eqcomi.mm"
include "dgr0.mm"
include "3netr4g.mm"
include "fveq2.mm"
include "necon3i.mm"
include "syl.mm"
include "eqid.mm"
include "fta1.mm"
include "syl2anc.mm"
include "simpld.mm"
include "abrexfi.mm"
include "rabssab.mm"
include "ssfi.mm"
include "sylancl.mm"
include "unfi.mm"
include "sylancr.mm"
include "1ex.mm"
include "snid.mm"
include "elun1.mm"
include "ne0i.mm"
include "mp2b.mm"
include "rpssre.mm"
include "sstri.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "sseldi.mm"
include "wn.mm"
include "0re.mm"
include "rpge0.mm"
include "rgen.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "ssralv.mm"
include "reximi.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "resubcld.mm"
include "recnd.mm"
include "subeq0ad.mm"
include "necon3abid.mm"
include "biimprd.mm"
include "impr.mm"
include "absrpcld.mm"
include "cc.mm"
include "simprl.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "plyf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elun2.mm"
include "infrelb.mm"
include "syl3anc.mm"
include "expr.mm"
include "orrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "orbi2d.mm"
include "imbi2d.mm"
include "eqeq1d.mm"
include "eqeq2.mm"
include "breq2d.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "cq.mm"
include "znq.mm"
include "qre.mm"
include "syl11.mm"
include "ralrimivv.mm"
include "simprr.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "adantr.mm"
include "simpllr.mm"
include "adantl.mm"
include "abscld.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "rpcnne0d.mm"
include "divid.mm"
include "nnge1d.mm"
include "eqbrtrd.mm"
include "lediv23d.mm"
include "simpr.mm"
include "letrd.mm"
include "orim2d.mm"
include "imim2d.mm"
include "ralimdvva.mm"
include "reximdva.mm"
include "mpd.mm"

theorem aalioulem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aalioulem2.a: |- N = ( deg ` F )
  assume aalioulem2.b: |- ( ph -> F e. ( Poly ` ZZ ) )
  assume aalioulem2.c: |- ( ph -> N e. NN )
  assume aalioulem2.d: |- ( ph -> A e. RR )

  disjoint ph x
  disjoint p ph
  disjoint ph q
  disjoint p x
  disjoint q x
  disjoint p q
  disjoint A x
  disjoint A p
  disjoint A q
  disjoint F x
  disjoint F p
  disjoint F q
  disjoint ph r
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint r x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint p r
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint d p
  disjoint q r
  disjoint a q
  disjoint b q
  disjoint c q
  disjoint d q
  disjoint a r
  disjoint b r
  disjoint c r
  disjoint d r
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint A r
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint F r
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  assert |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN ( ( F ` ( p / q ) ) = 0 -> ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_ ( abs ` ( A - ( p / q ) ) ) ) ) )

  proof
    wph
    vp
    cv
    #
    vq
    cv
    #
    cdiv
    co
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    cA
    @2
    wceq
    #
    vx
    cv
    #
    cA
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wo
    #
    wi
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    vx
    crp
    wrex
    #
    @4
    @5
    @6
    @1
    cN
    cexp
    co
    #
    cdiv
    co
    #
    @8
    cle
    wbr
    #
    wo
    #
    wi
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    vx
    crp
    wrex
    wph
    vr
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    cA
    @20
    wceq
    #
    @6
    cA
    @20
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wo
    #
    wi
    #
    vr
    cr
    wral
    #
    vx
    crp
    wrex
    #
    @13
    wph
    c1
    csn
    #
    va
    cv
    #
    cA
    vb
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    wceq
    #
    vb
    cF
    ccnv
    cc0
    csn
    cima
    #
    wrex
    #
    va
    crp
    crab
    #
    cun
    #
    cr
    clt
    cinf
    #
    crp
    wcel
    @22
    @23
    @41
    @25
    cle
    wbr
    #
    wo
    #
    wi
    #
    vr
    cr
    wral
    #
    @30
    wph
    @40
    crp
    @41
    @31
    @39
    crp
    c1
    crp
    wcel
    @31
    crp
    wss
    1rp
    c1
    crp
    snssi
    ax-mp
    @38
    va
    crp
    ssrab2
    unssi
    #
    wph
    cr
    clt
    wor
    #
    @40
    cfn
    wcel
    #
    @40
    c0
    wne
    #
    @40
    cr
    wss
    #
    @41
    @40
    wcel
    @47
    wph
    ltso
    a1i
    wph
    @31
    cfn
    wcel
    @39
    cfn
    wcel
    #
    @48
    c1
    snfi
    wph
    @38
    va
    cab
    #
    cfn
    wcel
    #
    @39
    @52
    wss
    @51
    wph
    @37
    cfn
    wcel
    #
    @53
    wph
    @54
    @37
    chash
    cfv
    cF
    cdgr
    cfv
    #
    cle
    wbr
    #
    wph
    cF
    cz
    cply
    cfv
    wcel
    #
    cF
    c0p
    wne
    #
    @54
    @56
    wa
    aalioulem2.b
    wph
    @55
    c0p
    cdgr
    cfv
    #
    wne
    @58
    wph
    cN
    cc0
    @55
    @59
    wph
    cN
    aalioulem2.c
    nnne0d
    cN
    @55
    aalioulem2.a
    eqcomi
    dgr0
    3netr4g
    cF
    c0p
    @55
    @59
    cF
    c0p
    cdgr
    fveq2
    necon3i
    syl
    @37
    cz
    cF
    @37
    eqid
    fta1
    syl2anc
    simpld
    vb
    va
    @37
    @35
    abrexfi
    syl
    @38
    va
    crp
    rabssab
    @52
    @39
    ssfi
    sylancl
    @31
    @39
    unfi
    sylancr
    @49
    wph
    c1
    @31
    wcel
    c1
    @40
    wcel
    @49
    c1
    1ex
    snid
    c1
    @31
    @39
    elun1
    @40
    c1
    ne0i
    mp2b
    a1i
    @50
    wph
    @40
    crp
    cr
    @46
    rpssre
    sstri
    #
    a1i
    cr
    @40
    clt
    fiinfcl
    syl13anc
    sseldi
    wph
    @44
    vr
    cr
    wph
    @20
    cr
    wcel
    #
    wa
    #
    @22
    @43
    @62
    @22
    wa
    #
    @23
    @42
    @62
    @22
    @23
    wn
    #
    @42
    @62
    @22
    @64
    wa
    #
    wa
    #
    @50
    vc
    cv
    #
    vd
    cv
    #
    cle
    wbr
    #
    vd
    @40
    wral
    #
    vc
    cr
    wrex
    #
    @25
    @40
    wcel
    #
    @42
    @50
    @66
    @60
    a1i
    @71
    @66
    @69
    vd
    crp
    wral
    #
    vc
    cr
    wrex
    #
    @71
    cc0
    cr
    wcel
    cc0
    @68
    cle
    wbr
    #
    vd
    crp
    wral
    #
    @74
    0re
    @75
    vd
    crp
    @68
    rpge0
    rgen
    @73
    @76
    vc
    cc0
    cr
    @67
    cc0
    wceq
    @69
    @75
    vd
    crp
    @67
    cc0
    @68
    cle
    breq1
    ralbidv
    rspcev
    mp2an
    @73
    @70
    vc
    cr
    @40
    crp
    wss
    @73
    @70
    wi
    @46
    @69
    vd
    @40
    crp
    ssralv
    ax-mp
    reximi
    ax-mp
    a1i
    @66
    @25
    @39
    wcel
    #
    @72
    @66
    @25
    crp
    wcel
    @25
    @35
    wceq
    #
    vb
    @37
    wrex
    #
    @77
    @66
    @24
    @66
    @24
    @66
    cA
    @20
    wph
    cA
    cr
    wcel
    #
    @61
    @65
    aalioulem2.d
    ad2antrr
    wph
    @61
    @65
    simplr
    #
    resubcld
    recnd
    @62
    @22
    @64
    @24
    cc0
    wne
    #
    @63
    @82
    @64
    @63
    @23
    @24
    cc0
    @63
    cA
    @20
    @63
    cA
    wph
    @80
    @61
    @22
    aalioulem2.d
    ad2antrr
    recnd
    @63
    @20
    wph
    @61
    @22
    simplr
    recnd
    subeq0ad
    necon3abid
    biimprd
    impr
    absrpcld
    @66
    @20
    @37
    wcel
    #
    @25
    @25
    wceq
    #
    @79
    @66
    @83
    @20
    cc
    wcel
    #
    @22
    @66
    @20
    @81
    recnd
    @62
    @22
    @64
    simprl
    @66
    cF
    cc
    wfn
    #
    @83
    @85
    @22
    wa
    wb
    wph
    @86
    @61
    @65
    wph
    cc
    cc
    cF
    wf
    #
    @86
    wph
    @57
    @87
    aalioulem2.b
    cz
    cF
    plyf
    syl
    cc
    cc
    cF
    ffn
    syl
    ad2antrr
    cc
    cc0
    @20
    cF
    fniniseg
    syl
    mpbir2and
    @25
    eqid
    @78
    @84
    vb
    @20
    @37
    @33
    @20
    wceq
    #
    @35
    @25
    @25
    @88
    @34
    @24
    cabs
    @33
    @20
    cA
    cmin
    oveq2
    fveq2d
    eqeq2d
    rspcev
    sylancl
    @38
    @79
    va
    @25
    crp
    @32
    @25
    wceq
    @36
    @78
    vb
    @37
    @32
    @25
    @35
    eqeq1
    rexbidv
    elrab
    sylanbrc
    @25
    @39
    @31
    elun2
    syl
    vc
    vd
    @25
    @40
    infrelb
    syl3anc
    expr
    orrd
    ex
    ralrimiva
    @29
    @45
    vx
    @41
    crp
    @6
    @41
    wceq
    #
    @28
    @44
    vr
    cr
    @89
    @27
    @43
    @22
    @89
    @26
    @42
    @23
    @6
    @41
    @25
    cle
    breq1
    orbi2d
    imbi2d
    ralbidv
    rspcev
    syl2anc
    @29
    @12
    vx
    crp
    @29
    @11
    vp
    vq
    cz
    cn
    @2
    cr
    wcel
    #
    @29
    @11
    @0
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    #
    @28
    @11
    vr
    @2
    cr
    @20
    @2
    wceq
    #
    @22
    @4
    @27
    @10
    @94
    @21
    @3
    cc0
    @20
    @2
    cF
    fveq2
    eqeq1d
    @94
    @23
    @5
    @26
    @9
    @20
    @2
    cA
    eqeq2
    @94
    @25
    @8
    @6
    cle
    @94
    @24
    @7
    cabs
    @20
    @2
    cA
    cmin
    oveq2
    fveq2d
    breq2d
    orbi12d
    imbi12d
    rspcv
    @93
    @2
    cq
    wcel
    @90
    @0
    @1
    znq
    @2
    qre
    syl
    #
    syl11
    ralrimivv
    reximi
    syl
    wph
    @12
    @19
    vx
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    #
    @11
    @18
    vp
    vq
    cz
    cn
    @97
    @93
    wa
    #
    @10
    @17
    @4
    @98
    @9
    @16
    @5
    @98
    @9
    @16
    @98
    @9
    wa
    #
    @15
    @6
    @8
    @98
    @15
    cr
    wcel
    @9
    @98
    @15
    @98
    @6
    @14
    wph
    @96
    @93
    simplr
    #
    @98
    @14
    @98
    @1
    cN
    @97
    @91
    @92
    simprr
    wph
    cN
    cn0
    wcel
    @96
    @93
    wph
    cN
    aalioulem2.c
    nnnn0d
    ad2antrr
    nnexpcld
    #
    nnrpd
    #
    rpdivcld
    rpred
    adantr
    @99
    @6
    wph
    @96
    @93
    @9
    simpllr
    rpred
    @98
    @8
    cr
    wcel
    @9
    @98
    @7
    @98
    @7
    @98
    cA
    @2
    wph
    @80
    @96
    @93
    aalioulem2.d
    ad2antrr
    @93
    @90
    @97
    @95
    adantl
    resubcld
    recnd
    abscld
    adantr
    @98
    @15
    @6
    cle
    wbr
    @9
    @98
    @6
    @6
    @14
    @96
    @6
    cr
    wcel
    wph
    @93
    @6
    rpre
    ad2antlr
    @100
    @102
    @98
    @6
    @6
    cdiv
    co
    #
    c1
    @14
    cle
    @98
    @6
    cc
    wcel
    @6
    cc0
    wne
    wa
    @103
    c1
    wceq
    @98
    @6
    @100
    rpcnne0d
    @6
    divid
    syl
    @98
    @14
    @101
    nnge1d
    eqbrtrd
    lediv23d
    adantr
    @98
    @9
    simpr
    letrd
    ex
    orim2d
    imim2d
    ralimdvva
    reximdva
    mpd
end
