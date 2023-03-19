include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cq.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "ccxp.mm"
include "cmpt.mm"
include "wceq.mm"
include "wrex.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "clog.mm"
include "cdiv.mm"
include "crp.mm"
include "cn.mm"
include "c2.mm"
include "cuz.mm"
include "wa.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnq.mm"
include "syl.mm"
include "qrngbas.mm"
include "abvcl.mm"
include "syl2anc.mm"
include "rplogcld.mm"
include "nnred.mm"
include "simprd.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "cmul.mm"
include "ce.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "qabvle.mm"
include "wne.mm"
include "nnne0d.mm"
include "qrng0.mm"
include "abvgt0.mm"
include "syl3anc.mm"
include "elrpd.mm"
include "reeflogd.mm"
include "nnrpd.mm"
include "3brtr4d.mm"
include "wb.mm"
include "relogcld.mm"
include "efle.mm"
include "mpbird.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1red.mm"
include "ledivmuld.mm"
include "syl5eqbr.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "cres.mm"
include "qabsabv.mm"
include "fvres.mm"
include "oveq1d.mm"
include "mpteq2ia.mm"
include "eqcomi.mm"
include "abvcxp.mm"
include "sylancr.mm"
include "cz.mm"
include "eluzelz.mm"
include "zq.mm"
include "fveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "adantl.mm"
include "simpr.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "recnd.mm"
include "cc.mm"
include "adantr.mm"
include "cxpefd.mm"
include "cif.mm"
include "ostth2lem4.mm"
include "ef0.mm"
include "0re.mm"
include "eflt.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "divcan1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "3eqtrrd.mm"
include "ostthlem1.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "rspcev.mm"

theorem ostth2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cF: class F
  let cJ: class J
  let cK: class K
  let cN: class N
  let vq: setvar q
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let cM: class M
  let vb: setvar b
  let vg: setvar g
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let cP: class P
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )
  assume ostth.k: |- K = ( x e. QQ |-> if ( x = 0 , 0 , 1 ) )
  assume ostth.1: |- ( ph -> F e. A )
  assume ostth2.2: |- ( ph -> N e. ( ZZ>= ` 2 ) )
  assume ostth2.3: |- ( ph -> 1 < ( F ` N ) )
  assume ostth2.4: |- R = ( ( log ` ( F ` N ) ) / ( log ` N ) )

  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a ph
  disjoint q x
  disjoint q y
  disjoint ph q
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint J a
  disjoint J y
  disjoint A a
  disjoint A q
  disjoint A x
  disjoint A y
  disjoint N x
  disjoint N y
  disjoint Q x
  disjoint Q y
  disjoint F a
  disjoint F q
  disjoint F y
  disjoint R a
  disjoint R q
  disjoint R y
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
  disjoint M x
  disjoint a b
  disjoint a k
  disjoint a n
  disjoint a p
  disjoint a z
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
  disjoint q z
  disjoint x z
  disjoint ph z
  disjoint a g
  disjoint g p
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint J p
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
  disjoint A k
  disjoint A n
  disjoint A p
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N z
  disjoint Q k
  disjoint Q n
  disjoint Q z
  disjoint Y k
  disjoint a j
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
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R p
  disjoint R z
  assert |- ( ph -> E. a e. ( 0 (,] 1 ) F = ( y e. QQ |-> ( ( abs ` y ) ^c a ) ) )

  proof
    wph
    cR
    cc0
    c1
    cioc
    co
    #
    wcel
    #
    cF
    vy
    cq
    vy
    cv
    #
    cabs
    cfv
    #
    cR
    ccxp
    co
    #
    cmpt
    #
    wceq
    #
    cF
    vy
    cq
    @3
    va
    cv
    #
    ccxp
    co
    #
    cmpt
    #
    wceq
    #
    va
    @0
    wrex
    wph
    cR
    cr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    cR
    c1
    cle
    wbr
    #
    @1
    wph
    cR
    wph
    cR
    cN
    cF
    cfv
    #
    clog
    cfv
    #
    cN
    clog
    cfv
    #
    cdiv
    co
    #
    crp
    ostth2.4
    wph
    @15
    @16
    wph
    @14
    wph
    cF
    cA
    wcel
    #
    cN
    cq
    wcel
    #
    @14
    cr
    wcel
    ostth.1
    wph
    cN
    cn
    wcel
    #
    @19
    wph
    @20
    c1
    cN
    clt
    wbr
    #
    wph
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    @20
    @21
    wa
    ostth2.2
    cN
    eluz2b2
    sylib
    #
    simpld
    #
    cN
    nnq
    syl
    #
    cA
    cq
    cQ
    cF
    cN
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvcl
    syl2anc
    #
    ostth2.3
    rplogcld
    #
    wph
    cN
    wph
    cN
    @25
    nnred
    wph
    @20
    @21
    @24
    simprd
    rplogcld
    #
    rpdivcld
    syl5eqel
    #
    rpred
    #
    wph
    cR
    @31
    rpgt0d
    wph
    cR
    @17
    c1
    cle
    ostth2.4
    wph
    @17
    c1
    cle
    wbr
    @15
    @16
    c1
    cmul
    co
    #
    cle
    wbr
    wph
    @15
    @16
    @33
    cle
    wph
    @15
    @16
    cle
    wbr
    #
    @15
    ce
    cfv
    #
    @16
    ce
    cfv
    #
    cle
    wbr
    #
    wph
    @14
    cN
    @35
    @36
    cle
    wph
    @18
    cN
    cn0
    wcel
    @14
    cN
    cle
    wbr
    ostth.1
    wph
    cN
    @25
    nnnn0d
    cA
    cQ
    cF
    cN
    qrng.q
    qabsabv.a
    qabvle
    syl2anc
    wph
    @14
    wph
    @14
    @28
    wph
    @18
    @19
    cN
    cc0
    wne
    cc0
    @14
    clt
    wbr
    ostth.1
    @26
    wph
    cN
    @25
    nnne0d
    cA
    cq
    cQ
    cF
    cN
    cc0
    qabsabv.a
    @27
    cQ
    qrng.q
    qrng0
    #
    abvgt0
    syl3anc
    elrpd
    reeflogd
    wph
    cN
    wph
    cN
    @25
    nnrpd
    #
    reeflogd
    3brtr4d
    wph
    @15
    cr
    wcel
    @16
    cr
    wcel
    @34
    @37
    wb
    wph
    @15
    @29
    rpred
    #
    wph
    cN
    @39
    relogcld
    @15
    @16
    efle
    syl2anc
    mpbird
    wph
    @16
    wph
    @16
    @30
    rpcnd
    mulid1d
    breqtrrd
    wph
    @15
    c1
    @16
    @40
    wph
    1red
    @30
    ledivmuld
    mpbird
    syl5eqbr
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @1
    @11
    @12
    @13
    w3a
    wb
    0xr
    1re
    cc0
    c1
    cR
    elioc2
    mp2an
    syl3anbrc
    #
    wph
    cA
    cQ
    vz
    cF
    @5
    qrng.q
    qabsabv.a
    ostth.1
    wph
    cabs
    cq
    cres
    #
    cA
    wcel
    @1
    @5
    cA
    wcel
    cA
    cQ
    qrng.q
    qabsabv.a
    qabsabv
    @41
    vy
    cA
    cq
    cQ
    cR
    @42
    @5
    qabsabv.a
    @27
    vy
    cq
    @2
    @42
    cfv
    #
    cR
    ccxp
    co
    #
    cmpt
    @5
    vy
    cq
    @44
    @4
    @2
    cq
    wcel
    @43
    @3
    cR
    ccxp
    @2
    cq
    cabs
    fvres
    oveq1d
    mpteq2ia
    eqcomi
    abvcxp
    sylancr
    wph
    vz
    cv
    #
    @22
    wcel
    #
    wa
    #
    @45
    @5
    cfv
    #
    @45
    cabs
    cfv
    #
    cR
    ccxp
    co
    #
    @45
    cR
    ccxp
    co
    #
    @45
    cF
    cfv
    #
    @46
    @48
    @50
    wceq
    #
    wph
    @46
    @45
    cz
    wcel
    #
    @45
    cq
    wcel
    #
    @53
    c2
    @45
    eluzelz
    #
    @45
    zq
    #
    vy
    @45
    @4
    @50
    cq
    @5
    @2
    @45
    wceq
    @3
    @49
    cR
    ccxp
    @2
    @45
    cabs
    fveq2
    oveq1d
    @5
    eqid
    @49
    cR
    ccxp
    ovex
    fvmpt
    3syl
    adantl
    @47
    @49
    @45
    cR
    ccxp
    @47
    @45
    @47
    @45
    @47
    @45
    cn
    wcel
    #
    c1
    @45
    clt
    wbr
    #
    @47
    @46
    @58
    @59
    wa
    wph
    @46
    simpr
    #
    @45
    eluz2b2
    sylib
    #
    simpld
    #
    nnred
    #
    @47
    @45
    @47
    @45
    @62
    nnnn0d
    nn0ge0d
    absidd
    oveq1d
    @47
    @51
    cR
    @45
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    @52
    clog
    cfv
    #
    ce
    cfv
    @52
    @47
    @45
    cR
    @47
    @45
    @63
    recnd
    @47
    @45
    @62
    nnne0d
    #
    wph
    cR
    cc
    wcel
    @46
    wph
    cR
    @31
    rpcnd
    adantr
    cxpefd
    @47
    @65
    @66
    ce
    @47
    @65
    @66
    @64
    cdiv
    co
    #
    @64
    cmul
    co
    @66
    @47
    cR
    @68
    @64
    cmul
    @47
    cR
    @68
    wceq
    cR
    @68
    cle
    wbr
    #
    @68
    cR
    cle
    wbr
    #
    @47
    c1
    @52
    clt
    wbr
    #
    @69
    @47
    vx
    cA
    cQ
    cR
    @68
    @52
    c1
    cle
    wbr
    c1
    @52
    cif
    #
    @16
    @64
    cdiv
    co
    #
    cF
    cJ
    cK
    @45
    cN
    vq
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    wph
    @18
    @46
    ostth.1
    adantr
    #
    wph
    @23
    @46
    ostth2.2
    adantr
    #
    wph
    c1
    @14
    clt
    wbr
    #
    @46
    ostth2.3
    adantr
    ostth2.4
    @60
    @68
    eqid
    #
    @72
    eqid
    @73
    eqid
    ostth2lem4
    #
    simprd
    @47
    @76
    @70
    @47
    vx
    cA
    cQ
    @68
    cR
    @14
    c1
    cle
    wbr
    c1
    @14
    cif
    #
    @64
    @16
    cdiv
    co
    #
    cF
    cJ
    cK
    cN
    @45
    vq
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    @74
    @60
    @47
    @71
    @69
    @78
    simpld
    @77
    @75
    ostth2.4
    @79
    eqid
    @80
    eqid
    ostth2lem4
    simprd
    @47
    cR
    @68
    wph
    @11
    @46
    @32
    adantr
    @47
    @66
    @64
    @47
    @52
    @47
    @52
    @47
    @18
    @55
    @52
    cr
    wcel
    @74
    @47
    @54
    @55
    @46
    @54
    wph
    @56
    adantl
    @57
    syl
    #
    cA
    cq
    cQ
    cF
    @45
    qabsabv.a
    @27
    abvcl
    syl2anc
    @47
    @18
    @55
    @45
    cc0
    wne
    cc0
    @52
    clt
    wbr
    @74
    @81
    @67
    cA
    cq
    cQ
    cF
    @45
    cc0
    qabsabv.a
    @27
    @38
    abvgt0
    syl3anc
    elrpd
    #
    relogcld
    #
    @47
    @45
    @47
    @45
    @62
    nnrpd
    #
    relogcld
    #
    @47
    @64
    @47
    cc0
    @64
    clt
    wbr
    #
    cc0
    ce
    cfv
    #
    @64
    ce
    cfv
    #
    clt
    wbr
    #
    @47
    @87
    c1
    @88
    clt
    ef0
    @47
    c1
    @45
    @88
    clt
    @47
    @58
    @59
    @61
    simprd
    @47
    @45
    @84
    reeflogd
    breqtrrd
    syl5eqbr
    @47
    cc0
    cr
    wcel
    @64
    cr
    wcel
    @86
    @89
    wb
    0re
    @85
    cc0
    @64
    eflt
    sylancr
    mpbird
    gt0ne0d
    #
    redivcld
    letri3d
    mpbir2and
    oveq1d
    @47
    @66
    @64
    @47
    @66
    @83
    recnd
    @47
    @64
    @85
    recnd
    @90
    divcan1d
    eqtrd
    fveq2d
    @47
    @52
    @82
    reeflogd
    3eqtrd
    3eqtrrd
    ostthlem1
    @10
    @6
    va
    cR
    @0
    @7
    cR
    wceq
    #
    @9
    @5
    cF
    @91
    vy
    cq
    @8
    @4
    @7
    cR
    @3
    ccxp
    oveq2
    mpteq2dv
    eqeq2d
    rspcev
    syl2anc
end
