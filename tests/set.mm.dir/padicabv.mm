include "cprime.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "wa.mm"
include "cq.mm"
include "caddc.mm"
include "cmul.mm"
include "cabv.mm"
include "cfv.mm"
include "wceq.mm"
include "a1i.mm"
include "cbs.mm"
include "qrngbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "qex.mm"
include "ccnfld.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "mp1i.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "c0g.mm"
include "qrng0.mm"
include "cdr.mm"
include "crg.mm"
include "qdrng.mm"
include "drngring.mm"
include "cv.mm"
include "cpc.mm"
include "cexp.mm"
include "cif.mm"
include "cr.mm"
include "0red.mm"
include "wn.mm"
include "ioossre.mm"
include "simpr.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "adantl.mm"
include "simpld.mm"
include "elrpd.mm"
include "rpne0d.mm"
include "cz.mm"
include "df-ne.mm"
include "pcqcl.mm"
include "adantlr.mm"
include "anassrs.mm"
include "sylan2br.mm"
include "reexpclzd.mm"
include "ifclda.mm"
include "fmptd.mm"
include "0z.mm"
include "zq.mm"
include "ax-mp.mm"
include "iftrue.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "3impb.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifbieq2d.mm"
include "ovex.mm"
include "ifex.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "pcqmul.mm"
include "3adant1r.mm"
include "cc.mm"
include "recnd.mm"
include "3adant3.mm"
include "simp1l.mm"
include "simp3l.mm"
include "simp3r.mm"
include "syl12anc.mm"
include "expaddz.mm"
include "syl22anc.mm"
include "simp2l.mm"
include "qmulcl.mm"
include "syl2anc.mm"
include "syl.mm"
include "qcn.mm"
include "simp2r.mm"
include "mulne0d.mm"
include "3expb.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "cle.mm"
include "breq1d.mm"
include "ifnefalse.mm"
include "adantr.mm"
include "zred.mm"
include "qaddcl.mm"
include "simpl1.mm"
include "readdcld.mm"
include "pcadd.mm"
include "crp.mm"
include "simprd.mm"
include "ltexp2rd.mm"
include "notbid.mm"
include "lenltd.mm"
include "3bitr4d.mm"
include "biimpa.mm"
include "syldan.mm"
include "rpexpcld.mm"
include "rpge0d.mm"
include "addge01d.mm"
include "mpbid.mm"
include "letrd.mm"
include "addcomd.mm"
include "addge02d.mm"
include "lecasei.mm"
include "eqbrtrd.mm"
include "rpaddcld.mm"
include "pm2.61ne.mm"
include "3brtr4d.mm"
include "isabvd.mm"

theorem padicabv
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cK: class K
  let vj: setvar j
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let wph: wff ph
  let vg: setvar g
  let cJ: class J
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.f: |- F = ( x e. QQ |-> if ( x = 0 , 0 , ( N ^ ( P pCnt x ) ) ) )

  disjoint A x
  disjoint N x
  disjoint Q x
  disjoint P x
  disjoint k n
  disjoint k p
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n p
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K k
  disjoint K n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint M j
  disjoint k x
  disjoint M k
  disjoint n x
  disjoint M n
  disjoint M x
  disjoint a b
  disjoint a k
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b k
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint k q
  disjoint k ph
  disjoint n q
  disjoint n ph
  disjoint p q
  disjoint p x
  disjoint p ph
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint ph q
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint a g
  disjoint J a
  disjoint g p
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint J p
  disjoint J y
  disjoint J z
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint T x
  disjoint U n
  disjoint U x
  disjoint X k
  disjoint X x
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A p
  disjoint A q
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q n
  disjoint Q y
  disjoint Q z
  disjoint Y k
  disjoint a j
  disjoint F a
  disjoint b g
  disjoint b j
  disjoint F b
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g q
  disjoint F g
  disjoint j p
  disjoint j q
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F p
  disjoint F q
  disjoint F y
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P q
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R p
  disjoint R q
  disjoint R y
  disjoint R z
  assert |- ( ( P e. Prime /\ N e. ( 0 (,) 1 ) ) -> F e. A )

  proof
    cP
    cprime
    wcel
    #
    cN
    cc0
    c1
    cioo
    co
    #
    wcel
    #
    wa
    #
    vy
    vz
    cA
    cq
    caddc
    cQ
    cmul
    cF
    cc0
    cA
    cQ
    cabv
    cfv
    wceq
    @3
    qabsabv.a
    a1i
    cq
    cQ
    cbs
    cfv
    wceq
    @3
    cQ
    qrng.q
    qrngbas
    a1i
    cq
    cvv
    wcel
    #
    caddc
    cQ
    cplusg
    cfv
    wceq
    @3
    qex
    cq
    caddc
    ccnfld
    cQ
    cvv
    qrng.q
    cnfldadd
    ressplusg
    mp1i
    @4
    cmul
    cQ
    cmulr
    cfv
    wceq
    @3
    qex
    cq
    ccnfld
    cQ
    cmul
    cvv
    qrng.q
    cnfldmul
    ressmulr
    mp1i
    cc0
    cQ
    c0g
    cfv
    wceq
    @3
    cQ
    qrng.q
    qrng0
    a1i
    cQ
    cdr
    wcel
    cQ
    crg
    wcel
    @3
    cQ
    qrng.q
    qdrng
    cQ
    drngring
    mp1i
    @3
    vx
    cq
    vx
    cv
    #
    cc0
    wceq
    #
    cc0
    cN
    cP
    @5
    cpc
    co
    #
    cexp
    co
    #
    cif
    #
    cr
    cF
    @3
    @5
    cq
    wcel
    #
    wa
    #
    @6
    cc0
    @8
    cr
    @11
    @6
    wa
    0red
    @11
    @6
    wn
    #
    wa
    cN
    @7
    @3
    cN
    cr
    wcel
    #
    @10
    @12
    @3
    @1
    cr
    cN
    cc0
    c1
    ioossre
    @0
    @2
    simpr
    sseldi
    #
    ad2antrr
    @3
    cN
    cc0
    wne
    #
    @10
    @12
    @3
    cN
    @3
    cN
    @14
    @3
    cc0
    cN
    clt
    wbr
    #
    cN
    c1
    clt
    wbr
    #
    @2
    @16
    @17
    wa
    @0
    cN
    cc0
    c1
    eliooord
    adantl
    #
    simpld
    #
    elrpd
    #
    rpne0d
    #
    ad2antrr
    @12
    @11
    @5
    cc0
    wne
    #
    @7
    cz
    wcel
    #
    @5
    cc0
    df-ne
    @3
    @10
    @22
    @23
    @0
    @10
    @22
    wa
    @23
    @2
    cP
    @5
    pcqcl
    adantlr
    anassrs
    sylan2br
    reexpclzd
    ifclda
    padic.f
    fmptd
    cc0
    cq
    wcel
    #
    cc0
    cF
    cfv
    cc0
    wceq
    @3
    cc0
    cz
    wcel
    @24
    0z
    cc0
    zq
    ax-mp
    vx
    cc0
    @9
    cc0
    cq
    cF
    @6
    cc0
    @8
    iftrue
    padic.f
    c0ex
    fvmpt
    mp1i
    @3
    vy
    cv
    #
    cq
    wcel
    #
    @25
    cc0
    wne
    #
    w3a
    #
    cc0
    cN
    cP
    @25
    cpc
    co
    #
    cexp
    co
    #
    @25
    cF
    cfv
    #
    clt
    @28
    @13
    @29
    cz
    wcel
    #
    @16
    cc0
    @30
    clt
    wbr
    @3
    @26
    @13
    @27
    @14
    3ad2ant1
    @3
    @26
    @27
    @32
    @0
    @26
    @27
    wa
    #
    @32
    @2
    cP
    @25
    pcqcl
    adantlr
    #
    3impb
    @3
    @26
    @16
    @27
    @19
    3ad2ant1
    cN
    @29
    expgt0
    syl3anc
    @28
    @31
    @25
    cc0
    wceq
    #
    cc0
    @30
    cif
    #
    @30
    @26
    @3
    @31
    @36
    wceq
    @27
    vx
    @25
    @9
    @36
    cq
    cF
    @5
    @25
    wceq
    #
    @6
    @35
    @8
    @30
    cc0
    @5
    @25
    cc0
    eqeq1
    @37
    @7
    @29
    cN
    cexp
    @5
    @25
    cP
    cpc
    oveq2
    oveq2d
    ifbieq2d
    padic.f
    @35
    cc0
    @30
    c0ex
    cN
    @29
    cexp
    ovex
    ifex
    fvmpt
    3ad2ant2
    @28
    @35
    cc0
    @30
    @28
    @25
    cc0
    @3
    @26
    @27
    simp3
    neneqd
    iffalsed
    eqtrd
    #
    breqtrrd
    @3
    @33
    vz
    cv
    #
    cq
    wcel
    #
    @39
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cN
    cP
    @25
    @39
    cmul
    co
    #
    cpc
    co
    #
    cexp
    co
    #
    @30
    cN
    cP
    @39
    cpc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @44
    cF
    cfv
    #
    @31
    @39
    cF
    cfv
    #
    cmul
    co
    @43
    @46
    cN
    @29
    @47
    caddc
    co
    #
    cexp
    co
    #
    @49
    @43
    @45
    @52
    cN
    cexp
    @0
    @33
    @42
    @45
    @52
    wceq
    @2
    @25
    @39
    cP
    pcqmul
    3adant1r
    oveq2d
    @43
    cN
    cc
    wcel
    #
    @15
    @32
    @47
    cz
    wcel
    #
    @53
    @49
    wceq
    @3
    @33
    @54
    @42
    @3
    cN
    @14
    recnd
    3ad2ant1
    @3
    @33
    @15
    @42
    @21
    3ad2ant1
    #
    @3
    @33
    @32
    @42
    @34
    3adant3
    #
    @43
    @0
    @40
    @41
    @55
    @0
    @2
    @33
    @42
    simp1l
    #
    @3
    @33
    @40
    @41
    simp3l
    #
    @3
    @33
    @40
    @41
    simp3r
    #
    cP
    @39
    pcqcl
    syl12anc
    #
    cN
    @29
    @47
    expaddz
    syl22anc
    eqtrd
    @43
    @50
    @44
    cc0
    wceq
    #
    cc0
    @46
    cif
    #
    @46
    @43
    @44
    cq
    wcel
    #
    @50
    @63
    wceq
    @43
    @26
    @40
    @64
    @3
    @26
    @27
    @42
    simp2l
    #
    @59
    @25
    @39
    qmulcl
    syl2anc
    vx
    @44
    @9
    @63
    cq
    cF
    @5
    @44
    wceq
    #
    @6
    @62
    @8
    @46
    cc0
    @5
    @44
    cc0
    eqeq1
    @66
    @7
    @45
    cN
    cexp
    @5
    @44
    cP
    cpc
    oveq2
    oveq2d
    ifbieq2d
    padic.f
    @62
    cc0
    @46
    c0ex
    cN
    @45
    cexp
    ovex
    ifex
    fvmpt
    syl
    @43
    @62
    cc0
    @46
    @43
    @44
    cc0
    @43
    @25
    @39
    @43
    @26
    @25
    cc
    wcel
    @65
    @25
    qcn
    syl
    #
    @43
    @40
    @39
    cc
    wcel
    @59
    @39
    qcn
    syl
    #
    @3
    @26
    @27
    @42
    simp2r
    @60
    mulne0d
    neneqd
    iffalsed
    eqtrd
    @43
    @31
    @30
    @51
    @48
    cmul
    @3
    @33
    @31
    @30
    wceq
    #
    @42
    @3
    @26
    @27
    @69
    @38
    3expb
    3adant3
    #
    @43
    @51
    @39
    cc0
    wceq
    #
    cc0
    @48
    cif
    #
    @48
    @43
    @40
    @51
    @72
    wceq
    @59
    vx
    @39
    @9
    @72
    cq
    cF
    @5
    @39
    wceq
    #
    @6
    @71
    @8
    @48
    cc0
    @5
    @39
    cc0
    eqeq1
    @73
    @7
    @47
    cN
    cexp
    @5
    @39
    cP
    cpc
    oveq2
    oveq2d
    ifbieq2d
    padic.f
    @71
    cc0
    @48
    c0ex
    cN
    @47
    cexp
    ovex
    ifex
    fvmpt
    syl
    @43
    @71
    cc0
    @48
    @43
    @39
    cc0
    @60
    neneqd
    iffalsed
    eqtrd
    #
    oveq12d
    3eqtr4d
    @43
    @25
    @39
    caddc
    co
    #
    cc0
    wceq
    #
    cc0
    cN
    cP
    @75
    cpc
    co
    #
    cexp
    co
    #
    cif
    #
    @30
    @48
    caddc
    co
    #
    @75
    cF
    cfv
    #
    @31
    @51
    caddc
    co
    cle
    @43
    @79
    @80
    cle
    wbr
    cc0
    @80
    cle
    wbr
    @75
    cc0
    @76
    @79
    cc0
    @80
    cle
    @76
    cc0
    @78
    iftrue
    breq1d
    @43
    @75
    cc0
    wne
    #
    wa
    #
    @79
    @78
    @80
    cle
    @82
    @79
    @78
    wceq
    @43
    @75
    cc0
    cc0
    @78
    ifnefalse
    adantl
    @83
    @78
    @80
    cle
    wbr
    @29
    @47
    @83
    @29
    @43
    @32
    @82
    @57
    adantr
    #
    zred
    #
    @83
    @47
    @43
    @55
    @82
    @61
    adantr
    #
    zred
    #
    @83
    @29
    @47
    cle
    wbr
    #
    wa
    #
    @78
    @30
    @80
    @89
    cN
    @77
    @43
    @13
    @82
    @88
    @3
    @33
    @13
    @42
    @14
    3ad2ant1
    ad2antrr
    #
    @43
    @15
    @82
    @88
    @56
    ad2antrr
    #
    @83
    @77
    cz
    wcel
    #
    @88
    @83
    @0
    @75
    cq
    wcel
    #
    @82
    @92
    @43
    @0
    @82
    @58
    adantr
    #
    @43
    @93
    @82
    @43
    @26
    @40
    @93
    @65
    @59
    @25
    @39
    qaddcl
    syl2anc
    #
    adantr
    @43
    @82
    simpr
    cP
    @75
    pcqcl
    syl12anc
    #
    adantr
    reexpclzd
    @89
    cN
    @29
    @90
    @91
    @83
    @32
    @88
    @84
    adantr
    reexpclzd
    @83
    @80
    cr
    wcel
    #
    @88
    @83
    @30
    @48
    @83
    cN
    @29
    @83
    @3
    @13
    @3
    @33
    @42
    @82
    simpl1
    #
    @14
    syl
    #
    @83
    @3
    @15
    @98
    @21
    syl
    #
    @84
    reexpclzd
    #
    @83
    cN
    @47
    @99
    @100
    @86
    reexpclzd
    #
    readdcld
    #
    adantr
    @83
    @88
    @29
    @77
    cle
    wbr
    #
    @78
    @30
    cle
    wbr
    #
    @89
    @25
    @39
    cP
    @83
    @0
    @88
    @94
    adantr
    @43
    @26
    @82
    @88
    @65
    ad2antrr
    @43
    @40
    @82
    @88
    @59
    ad2antrr
    @83
    @88
    simpr
    pcadd
    @83
    @104
    @105
    @83
    @77
    @29
    clt
    wbr
    #
    wn
    @30
    @78
    clt
    wbr
    #
    wn
    @104
    @105
    @83
    @106
    @107
    @83
    cN
    @77
    @29
    @83
    @3
    cN
    crp
    wcel
    #
    @98
    @20
    syl
    #
    @84
    @96
    @83
    @3
    @17
    @98
    @3
    @16
    @17
    @18
    simprd
    syl
    #
    ltexp2rd
    notbid
    @83
    @29
    @77
    @85
    @83
    @77
    @96
    zred
    #
    lenltd
    @83
    @78
    @30
    @83
    cN
    @77
    @99
    @100
    @96
    reexpclzd
    #
    @101
    lenltd
    3bitr4d
    biimpa
    syldan
    @83
    @30
    @80
    cle
    wbr
    #
    @88
    @83
    cc0
    @48
    cle
    wbr
    @113
    @83
    @48
    @43
    @48
    crp
    wcel
    @82
    @43
    cN
    @47
    @3
    @33
    @108
    @42
    @20
    3ad2ant1
    #
    @61
    rpexpcld
    #
    adantr
    rpge0d
    @83
    @30
    @48
    @101
    @102
    addge01d
    mpbid
    adantr
    letrd
    @83
    @47
    @29
    cle
    wbr
    #
    wa
    #
    @78
    @48
    @80
    @83
    @78
    cr
    wcel
    @116
    @112
    adantr
    @83
    @48
    cr
    wcel
    @116
    @102
    adantr
    @83
    @97
    @116
    @103
    adantr
    @83
    @116
    @47
    @77
    cle
    wbr
    #
    @78
    @48
    cle
    wbr
    #
    @117
    @47
    cP
    @39
    @25
    caddc
    co
    #
    cpc
    co
    #
    @77
    cle
    @117
    @39
    @25
    cP
    @83
    @0
    @116
    @94
    adantr
    @43
    @40
    @82
    @116
    @59
    ad2antrr
    @43
    @26
    @82
    @116
    @65
    ad2antrr
    @83
    @116
    simpr
    pcadd
    @43
    @77
    @121
    wceq
    @82
    @116
    @43
    @75
    @120
    cP
    cpc
    @43
    @25
    @39
    @67
    @68
    addcomd
    oveq2d
    ad2antrr
    breqtrrd
    @83
    @118
    @119
    @83
    @77
    @47
    clt
    wbr
    #
    wn
    @48
    @78
    clt
    wbr
    #
    wn
    @118
    @119
    @83
    @122
    @123
    @83
    cN
    @77
    @47
    @109
    @86
    @96
    @110
    ltexp2rd
    notbid
    @83
    @47
    @77
    @87
    @111
    lenltd
    @83
    @78
    @48
    @112
    @102
    lenltd
    3bitr4d
    biimpa
    syldan
    @83
    @48
    @80
    cle
    wbr
    #
    @116
    @83
    cc0
    @30
    cle
    wbr
    @124
    @83
    @30
    @43
    @30
    crp
    wcel
    @82
    @43
    cN
    @29
    @114
    @57
    rpexpcld
    #
    adantr
    rpge0d
    @83
    @48
    @30
    @102
    @101
    addge02d
    mpbid
    adantr
    letrd
    lecasei
    eqbrtrd
    @43
    @80
    @43
    @30
    @48
    @125
    @115
    rpaddcld
    rpge0d
    pm2.61ne
    @43
    @93
    @81
    @79
    wceq
    @95
    vx
    @75
    @9
    @79
    cq
    cF
    @5
    @75
    wceq
    #
    @6
    @76
    @8
    @78
    cc0
    @5
    @75
    cc0
    eqeq1
    @126
    @7
    @77
    cN
    cexp
    @5
    @75
    cP
    cpc
    oveq2
    oveq2d
    ifbieq2d
    padic.f
    @76
    cc0
    @78
    c0ex
    cN
    @77
    cexp
    ovex
    ifex
    fvmpt
    syl
    @43
    @31
    @30
    @51
    @48
    caddc
    @70
    @74
    oveq12d
    3brtr4d
    isabvd
end
