include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "raleqbidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "c2.mm"
include "cuz.mm"
include "cn.mm"
include "eluz2nn.mm"
include "syl.mm"
include "nncnd.mm"
include "exp0d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "0le0.mm"
include "a1i.mm"
include "qrng0.mm"
include "abv0.mm"
include "mul01d.mm"
include "cc.mm"
include "cif.mm"
include "cr.mm"
include "1re.mm"
include "cq.mm"
include "nnq.mm"
include "qrngbas.mm"
include "abvcl.mm"
include "syl2anc.mm"
include "ifcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "recnd.mm"
include "0nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "fveq2.mm"
include "cbvralv.mm"
include "cmo.mm"
include "cdiv.mm"
include "cfl.mm"
include "ad2antrr.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad2antrl.mm"
include "zq.mm"
include "simplr.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "reexpcld.mm"
include "zred.mm"
include "nndivred.mm"
include "flcld.mm"
include "remulcld.mm"
include "readdcld.mm"
include "nnred.mm"
include "nn0p1nn.mm"
include "ad2antlr.mm"
include "peano2nn0.mm"
include "qmulcl.mm"
include "cvv.mm"
include "cplusg.mm"
include "qex.mm"
include "ccnfld.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "abvtri.mm"
include "syl3anc.mm"
include "crp.mm"
include "nnrpd.mm"
include "modval.mm"
include "qcn.mm"
include "npcand.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "abvmul.mm"
include "qabvexp.mm"
include "3brtr3d.mm"
include "nn0re.mm"
include "zmodfz.mm"
include "simprr.mm"
include "rspcv.mm"
include "sylc.mm"
include "mulcomd.mm"
include "abvge0.mm"
include "expge0d.mm"
include "clt.mm"
include "elfzle1.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "flge0nn0.mm"
include "qabvle.mm"
include "w3a.mm"
include "simprl.mm"
include "wb.mm"
include "0z.mm"
include "nnzd.mm"
include "elfzm11.mm"
include "mpbid.mm"
include "simp3d.mm"
include "expp1d.mm"
include "breqtrd.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "fllt.mm"
include "ltled.mm"
include "letrd.mm"
include "lemul1ad.mm"
include "eqbrtrd.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "max1.mm"
include "syl6breqr.mm"
include "leexp1a.mm"
include "syl32anc.mm"
include "lemul2ad.mm"
include "le2addd.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "adddid.mm"
include "mulid1d.mm"
include "mulcld.mm"
include "adddird.mm"
include "breqtrrd.mm"
include "max2.mm"
include "nn0z.mm"
include "uzid.mm"
include "peano2uz.mm"
include "leexp2ad.mm"
include "nnmulcld.mm"
include "lemul2.mm"
include "expr.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"
include "rspccv.mm"
include "3impia.mm"

theorem ostth2lem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cU: class U
  let cP: class P
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )
  assume ostth.k: |- K = ( x e. QQ |-> if ( x = 0 , 0 , 1 ) )
  assume ostth.1: |- ( ph -> F e. A )
  assume ostth2.2: |- ( ph -> N e. ( ZZ>= ` 2 ) )
  assume ostth2.3: |- ( ph -> 1 < ( F ` N ) )
  assume ostth2.4: |- R = ( ( log ` ( F ` N ) ) / ( log ` N ) )
  assume ostth2.5: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume ostth2.6: |- S = ( ( log ` ( F ` M ) ) / ( log ` M ) )
  assume ostth2.7: |- T = if ( ( F ` M ) <_ 1 , 1 , ( F ` M ) )

  disjoint M x
  disjoint q x
  disjoint ph q
  disjoint ph x
  disjoint T x
  disjoint X x
  disjoint A q
  disjoint A x
  disjoint N x
  disjoint Q x
  disjoint F q
  disjoint R q
  disjoint F x
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
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
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
  disjoint U n
  disjoint U x
  disjoint X k
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A p
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
  disjoint F y
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R p
  disjoint R y
  disjoint R z
  assert |- ( ( ph /\ X e. NN0 /\ Y e. ( 0 ... ( ( M ^ X ) - 1 ) ) ) -> ( F ` Y ) <_ ( ( M x. X ) x. ( T ^ X ) ) )

  proof
    wph
    cX
    cn0
    wcel
    #
    cY
    cc0
    cM
    cX
    cexp
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    cY
    cF
    cfv
    #
    cM
    cX
    cmul
    co
    #
    cT
    cX
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wph
    @0
    wa
    vk
    cv
    #
    cF
    cfv
    #
    @8
    cle
    wbr
    #
    vk
    @3
    wral
    #
    @4
    @9
    wi
    @0
    wph
    @13
    wph
    @11
    cM
    vx
    cv
    #
    cmul
    co
    #
    cT
    @14
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vk
    cc0
    cM
    @14
    cexp
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @11
    cM
    cc0
    cmul
    co
    #
    cT
    cc0
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vk
    cc0
    cM
    cc0
    cexp
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @11
    cM
    vn
    cv
    #
    cmul
    co
    #
    cT
    @31
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vk
    cc0
    cM
    @31
    cexp
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @11
    cM
    @31
    c1
    caddc
    co
    #
    cmul
    co
    #
    cT
    @40
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vk
    cc0
    cM
    @40
    cexp
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wi
    wph
    @13
    wi
    vx
    vn
    cX
    @14
    cc0
    wceq
    #
    @22
    @30
    wph
    @49
    @18
    @26
    vk
    @21
    @29
    @49
    @20
    @28
    cc0
    cfz
    @49
    @19
    @27
    c1
    cmin
    @14
    cc0
    cM
    cexp
    oveq2
    oveq1d
    oveq2d
    @49
    @17
    @25
    @11
    cle
    @49
    @15
    @23
    @16
    @24
    cmul
    @14
    cc0
    cM
    cmul
    oveq2
    @14
    cc0
    cT
    cexp
    oveq2
    oveq12d
    breq2d
    raleqbidv
    imbi2d
    vx
    vn
    weq
    #
    @22
    @39
    wph
    @50
    @18
    @35
    vk
    @21
    @38
    @50
    @20
    @37
    cc0
    cfz
    @50
    @19
    @36
    c1
    cmin
    @14
    @31
    cM
    cexp
    oveq2
    oveq1d
    oveq2d
    @50
    @17
    @34
    @11
    cle
    @50
    @15
    @32
    @16
    @33
    cmul
    @14
    @31
    cM
    cmul
    oveq2
    @14
    @31
    cT
    cexp
    oveq2
    oveq12d
    breq2d
    raleqbidv
    imbi2d
    @14
    @40
    wceq
    #
    @22
    @48
    wph
    @51
    @18
    @44
    vk
    @21
    @47
    @51
    @20
    @46
    cc0
    cfz
    @51
    @19
    @45
    c1
    cmin
    @14
    @40
    cM
    cexp
    oveq2
    oveq1d
    oveq2d
    @51
    @17
    @43
    @11
    cle
    @51
    @15
    @41
    @16
    @42
    cmul
    @14
    @40
    cM
    cmul
    oveq2
    @14
    @40
    cT
    cexp
    oveq2
    oveq12d
    breq2d
    raleqbidv
    imbi2d
    @14
    cX
    wceq
    #
    @22
    @13
    wph
    @52
    @18
    @12
    vk
    @21
    @3
    @52
    @20
    @2
    cc0
    cfz
    @52
    @19
    @1
    c1
    cmin
    @14
    cX
    cM
    cexp
    oveq2
    oveq1d
    oveq2d
    @52
    @17
    @8
    @11
    cle
    @52
    @15
    @6
    @16
    @7
    cmul
    @14
    cX
    cM
    cmul
    oveq2
    @14
    cX
    cT
    cexp
    oveq2
    oveq12d
    breq2d
    raleqbidv
    imbi2d
    wph
    @26
    vk
    @29
    wph
    @10
    @29
    wcel
    @10
    cc0
    cc0
    cfz
    co
    #
    wcel
    #
    @26
    wph
    @29
    @53
    @10
    wph
    @28
    cc0
    cc0
    cfz
    wph
    @28
    c1
    c1
    cmin
    co
    cc0
    wph
    @27
    c1
    c1
    cmin
    wph
    cM
    wph
    cM
    wph
    cM
    c2
    cuz
    cfv
    wcel
    cM
    cn
    wcel
    #
    ostth2.5
    cM
    eluz2nn
    syl
    #
    nncnd
    #
    exp0d
    oveq1d
    1m1e0
    syl6eq
    oveq2d
    eleq2d
    wph
    @26
    @54
    cc0
    cF
    cfv
    #
    @25
    cle
    wbr
    wph
    cc0
    cc0
    @58
    @25
    cle
    cc0
    cc0
    cle
    wbr
    wph
    0le0
    a1i
    wph
    cF
    cA
    wcel
    #
    @58
    cc0
    wceq
    ostth.1
    cA
    cQ
    cF
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrng0
    abv0
    syl
    wph
    @25
    cc0
    @24
    cmul
    co
    cc0
    wph
    @23
    cc0
    @24
    cmul
    wph
    cM
    @57
    mul01d
    oveq1d
    wph
    @24
    wph
    cT
    cc
    wcel
    cc0
    cn0
    wcel
    @24
    cc
    wcel
    wph
    cT
    wph
    cT
    cM
    cF
    cfv
    #
    c1
    cle
    wbr
    #
    c1
    @60
    cif
    #
    cr
    ostth2.7
    wph
    c1
    cr
    wcel
    #
    @60
    cr
    wcel
    #
    @62
    cr
    wcel
    1re
    wph
    @59
    cM
    cq
    wcel
    #
    @64
    ostth.1
    wph
    @55
    @65
    @56
    cM
    nnq
    #
    syl
    cA
    cq
    cQ
    cF
    cM
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvcl
    #
    syl2anc
    @61
    c1
    @60
    cr
    ifcl
    sylancr
    syl5eqel
    #
    recnd
    0nn0
    cT
    cc0
    expcl
    sylancl
    mul02d
    eqtrd
    3brtr4d
    @54
    @11
    @58
    @25
    cle
    @54
    @10
    cc0
    cF
    @10
    cc0
    elfz1eq
    fveq2d
    breq1d
    syl5ibrcom
    sylbid
    ralrimiv
    @31
    cn0
    wcel
    #
    wph
    @39
    @48
    wph
    @70
    @39
    @48
    wi
    @39
    vj
    cv
    #
    cF
    cfv
    #
    @34
    cle
    wbr
    #
    vj
    @38
    wral
    #
    wph
    @70
    wa
    #
    @48
    @35
    @73
    vk
    vj
    @38
    vk
    vj
    weq
    @11
    @72
    @34
    cle
    @10
    @71
    cF
    fveq2
    breq1d
    cbvralv
    @75
    @74
    @44
    vk
    @47
    @75
    @10
    @47
    wcel
    #
    @74
    @44
    @75
    @76
    @74
    wa
    #
    wa
    #
    @11
    @10
    @36
    cmo
    co
    #
    cF
    cfv
    #
    @60
    @31
    cexp
    co
    #
    @10
    @36
    cdiv
    co
    #
    cfl
    cfv
    #
    cF
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @43
    @78
    @59
    @10
    cq
    wcel
    #
    @11
    cr
    wcel
    wph
    @59
    @70
    @77
    ostth.1
    ad2antrr
    #
    @78
    @10
    cz
    wcel
    #
    @87
    @76
    @89
    @75
    @74
    @10
    cc0
    @46
    elfzelz
    ad2antrl
    #
    @10
    zq
    syl
    cA
    cq
    cQ
    cF
    @10
    qabsabv.a
    @67
    abvcl
    syl2anc
    @78
    @80
    @85
    @78
    @59
    @79
    cq
    wcel
    #
    @80
    cr
    wcel
    @88
    @78
    @79
    cz
    wcel
    @91
    @78
    @79
    @78
    @10
    @36
    @90
    @78
    cM
    @31
    wph
    @55
    @70
    @77
    @56
    ad2antrr
    #
    wph
    @70
    @77
    simplr
    #
    nnexpcld
    #
    zmodcld
    nn0zd
    @79
    zq
    syl
    #
    cA
    cq
    cQ
    cF
    @79
    qabsabv.a
    @67
    abvcl
    syl2anc
    #
    @78
    @81
    @84
    @78
    @60
    @31
    @78
    @59
    @65
    @64
    @88
    @78
    @55
    @65
    @92
    @66
    syl
    #
    @68
    syl2anc
    #
    @93
    reexpcld
    #
    @78
    @59
    @83
    cq
    wcel
    #
    @84
    cr
    wcel
    @88
    @78
    @83
    cz
    wcel
    @100
    @78
    @82
    @78
    @10
    @36
    @78
    @10
    @90
    zred
    #
    @94
    nndivred
    #
    flcld
    #
    @83
    zq
    syl
    #
    cA
    cq
    cQ
    cF
    @83
    qabsabv.a
    @67
    abvcl
    syl2anc
    #
    remulcld
    #
    readdcld
    #
    @78
    @41
    @42
    @78
    cM
    @40
    @78
    cM
    @92
    nnred
    #
    @78
    @40
    @70
    @40
    cn
    wcel
    wph
    @77
    @31
    nn0p1nn
    ad2antlr
    #
    nnred
    remulcld
    #
    @78
    cT
    @40
    wph
    cT
    cr
    wcel
    #
    @70
    @77
    @69
    ad2antrr
    #
    @70
    @40
    cn0
    wcel
    wph
    @77
    @31
    peano2nn0
    ad2antlr
    #
    reexpcld
    #
    remulcld
    #
    @78
    @79
    @36
    @83
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @80
    @116
    cF
    cfv
    #
    caddc
    co
    #
    @11
    @86
    cle
    @78
    @59
    @91
    @116
    cq
    wcel
    #
    @118
    @120
    cle
    wbr
    @88
    @95
    @78
    @36
    cq
    wcel
    #
    @100
    @121
    @78
    @36
    cn
    wcel
    #
    @122
    @94
    @36
    nnq
    syl
    #
    @104
    @36
    @83
    qmulcl
    syl2anc
    #
    cA
    cq
    caddc
    cQ
    cF
    @79
    @116
    qabsabv.a
    @67
    cq
    cvv
    wcel
    #
    caddc
    cQ
    cplusg
    cfv
    wceq
    qex
    cq
    caddc
    ccnfld
    cQ
    cvv
    qrng.q
    cnfldadd
    ressplusg
    ax-mp
    abvtri
    syl3anc
    @78
    @117
    @10
    cF
    @78
    @117
    @10
    @116
    cmin
    co
    #
    @116
    caddc
    co
    @10
    @78
    @79
    @127
    @116
    caddc
    @78
    @10
    cr
    wcel
    #
    @36
    crp
    wcel
    @79
    @127
    wceq
    @101
    @78
    @36
    @94
    nnrpd
    @10
    @36
    modval
    syl2anc
    oveq1d
    @78
    @10
    @116
    @78
    @10
    @101
    recnd
    @78
    @121
    @116
    cc
    wcel
    @125
    @116
    qcn
    syl
    npcand
    eqtrd
    fveq2d
    @78
    @119
    @85
    @80
    caddc
    @78
    @119
    @36
    cF
    cfv
    #
    @84
    cmul
    co
    #
    @85
    @78
    @59
    @122
    @100
    @119
    @130
    wceq
    @88
    @124
    @104
    cA
    cq
    cQ
    cmul
    cF
    @36
    @83
    qabsabv.a
    @67
    @126
    cmul
    cQ
    cmulr
    cfv
    wceq
    qex
    cq
    ccnfld
    cQ
    cmul
    cvv
    qrng.q
    cnfldmul
    ressmulr
    ax-mp
    abvmul
    syl3anc
    @78
    @129
    @81
    @84
    cmul
    @78
    @59
    @65
    @70
    @129
    @81
    wceq
    @88
    @97
    @93
    cA
    cQ
    cF
    cM
    @31
    qrng.q
    qabsabv.a
    qabvexp
    syl3anc
    oveq1d
    eqtrd
    oveq2d
    3brtr3d
    @78
    @86
    @41
    @33
    cmul
    co
    #
    @43
    @107
    @78
    @41
    @33
    @110
    @78
    cT
    @31
    @112
    @93
    reexpcld
    #
    remulcld
    @115
    @78
    @86
    @34
    cM
    @33
    cmul
    co
    #
    caddc
    co
    #
    @131
    cle
    @78
    @80
    @85
    @34
    @133
    @96
    @106
    @78
    @32
    @33
    @78
    cM
    @31
    @108
    @70
    @31
    cr
    wcel
    wph
    @77
    @31
    nn0re
    ad2antlr
    remulcld
    @132
    remulcld
    @78
    cM
    @33
    @108
    @132
    remulcld
    #
    @78
    @79
    @38
    wcel
    #
    @74
    @80
    @34
    cle
    wbr
    #
    @78
    @89
    @123
    @136
    @90
    @94
    @10
    @36
    zmodfz
    syl2anc
    @75
    @76
    @74
    simprr
    @73
    @137
    vj
    @79
    @38
    @71
    @79
    wceq
    @72
    @80
    @34
    cle
    @71
    @79
    cF
    fveq2
    breq1d
    rspcv
    sylc
    @78
    @85
    cM
    @81
    cmul
    co
    #
    @133
    @106
    @78
    cM
    @81
    @108
    @99
    remulcld
    @135
    @78
    @85
    @84
    @81
    cmul
    co
    @138
    cle
    @78
    @81
    @84
    @78
    @81
    @99
    recnd
    @78
    @84
    @105
    recnd
    mulcomd
    @78
    @84
    cM
    @81
    @105
    @108
    @99
    @78
    @60
    @31
    @98
    @93
    @78
    @59
    @65
    cc0
    @60
    cle
    wbr
    #
    @88
    @97
    cA
    cq
    cQ
    cF
    cM
    qabsabv.a
    @67
    abvge0
    syl2anc
    #
    expge0d
    @78
    @84
    @83
    cM
    @105
    @78
    @83
    @103
    zred
    #
    @108
    @78
    @59
    @83
    cn0
    wcel
    #
    @84
    @83
    cle
    wbr
    @88
    @78
    @82
    cr
    wcel
    #
    cc0
    @82
    cle
    wbr
    #
    @142
    @102
    @78
    @128
    cc0
    @10
    cle
    wbr
    #
    @36
    cr
    wcel
    #
    cc0
    @36
    clt
    wbr
    #
    @144
    @101
    @76
    @145
    @75
    @74
    @10
    cc0
    @46
    elfzle1
    ad2antrl
    @78
    @36
    @94
    nnred
    #
    @78
    @36
    @94
    nngt0d
    #
    @10
    @36
    divge0
    syl22anc
    @82
    flge0nn0
    syl2anc
    cA
    cQ
    cF
    @83
    qrng.q
    qabsabv.a
    qabvle
    syl2anc
    @78
    @83
    cM
    @141
    @108
    @78
    @82
    cM
    clt
    wbr
    #
    @83
    cM
    clt
    wbr
    #
    @78
    @150
    @10
    @36
    cM
    cmul
    co
    #
    clt
    wbr
    #
    @78
    @10
    @45
    @152
    clt
    @78
    @89
    @145
    @10
    @45
    clt
    wbr
    #
    @78
    @76
    @89
    @145
    @154
    w3a
    #
    @75
    @76
    @74
    simprl
    @78
    cc0
    cz
    wcel
    @45
    cz
    wcel
    @76
    @155
    wb
    0z
    @78
    @45
    @78
    cM
    @40
    @92
    @113
    nnexpcld
    nnzd
    @10
    cc0
    @45
    elfzm11
    sylancr
    mpbid
    simp3d
    @78
    cM
    @31
    @78
    cM
    @92
    nncnd
    #
    @93
    expp1d
    breqtrd
    @78
    @128
    cM
    cr
    wcel
    @146
    @147
    @150
    @153
    wb
    @101
    @108
    @148
    @149
    @10
    cM
    @36
    ltdivmul
    syl112anc
    mpbird
    @78
    @143
    cM
    cz
    wcel
    @150
    @151
    wb
    @102
    @78
    cM
    @92
    nnzd
    @82
    cM
    fllt
    syl2anc
    mpbid
    ltled
    letrd
    lemul1ad
    eqbrtrd
    @78
    @81
    @33
    cM
    @99
    @132
    @108
    @78
    cM
    @78
    cM
    @92
    nnnn0d
    nn0ge0d
    @78
    @64
    @111
    @70
    @139
    @60
    cT
    cle
    wbr
    @81
    @33
    cle
    wbr
    @98
    @112
    @93
    @140
    @78
    @60
    @62
    cT
    cle
    @78
    @64
    @63
    @60
    @62
    cle
    wbr
    @98
    1re
    @60
    c1
    max1
    sylancl
    ostth2.7
    syl6breqr
    @60
    cT
    @31
    leexp1a
    syl32anc
    lemul2ad
    letrd
    le2addd
    @78
    @131
    @32
    cM
    caddc
    co
    #
    @33
    cmul
    co
    @134
    @78
    @41
    @157
    @33
    cmul
    @78
    @41
    @32
    cM
    c1
    cmul
    co
    #
    caddc
    co
    @157
    @78
    cM
    @31
    c1
    @156
    @70
    @31
    cc
    wcel
    wph
    @77
    @31
    nn0cn
    ad2antlr
    #
    @78
    1cnd
    adddid
    @78
    @158
    cM
    @32
    caddc
    @78
    cM
    @156
    mulid1d
    oveq2d
    eqtrd
    oveq1d
    @78
    @32
    cM
    @33
    @78
    cM
    @31
    @156
    @159
    mulcld
    @156
    @78
    @33
    @132
    recnd
    adddird
    eqtrd
    breqtrrd
    @78
    @33
    @42
    cle
    wbr
    #
    @131
    @43
    cle
    wbr
    #
    @78
    cT
    @31
    @40
    @112
    @78
    c1
    @62
    cT
    cle
    @78
    @64
    @63
    c1
    @62
    cle
    wbr
    @98
    1re
    @60
    c1
    max2
    sylancl
    ostth2.7
    syl6breqr
    @78
    @31
    @31
    cuz
    cfv
    #
    wcel
    #
    @40
    @162
    wcel
    @78
    @31
    cz
    wcel
    #
    @163
    @70
    @164
    wph
    @77
    @31
    nn0z
    ad2antlr
    @31
    uzid
    syl
    @31
    @31
    peano2uz
    syl
    leexp2ad
    @78
    @33
    cr
    wcel
    @42
    cr
    wcel
    @41
    cr
    wcel
    cc0
    @41
    clt
    wbr
    @160
    @161
    wb
    @132
    @114
    @110
    @78
    @41
    @78
    cM
    @40
    @92
    @109
    nnmulcld
    nngt0d
    @33
    @42
    @41
    lemul2
    syl112anc
    mpbid
    letrd
    letrd
    expr
    ralrimdva
    syl5bi
    expcom
    a2d
    nn0ind
    impcom
    @12
    @9
    vk
    cY
    @3
    @10
    cY
    wceq
    @11
    @5
    @8
    cle
    @10
    cY
    cF
    fveq2
    breq1d
    rspccv
    syl
    3impia
end
