include "wcel.mm"
include "wceq.mm"
include "cq.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "ccxp.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "wrex.mm"
include "crn.mm"
include "crp.mm"
include "w3o.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "wa.mm"
include "clog.mm"
include "cdiv.mm"
include "simpl.mm"
include "wn.mm"
include "c2.mm"
include "cuz.mm"
include "1re.mm"
include "ltnri.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "qrng1.mm"
include "qrng0.mm"
include "abv1z.mm"
include "mpan2.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "adantr.mm"
include "simprr.mm"
include "fveq2.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "wo.mm"
include "simprl.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "eqid.mm"
include "ostth2.mm"
include "rexlimdvaa.mm"
include "3mix2.mm"
include "syl6.mm"
include "wral.mm"
include "ralnex.mm"
include "cprime.mm"
include "cneg.mm"
include "cle.mm"
include "cif.mm"
include "simpll.mm"
include "simplr.mm"
include "weq.mm"
include "notbid.mm"
include "cbvralv.mm"
include "ostth3.mm"
include "expr.mm"
include "reximdva.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "padicabvf.mm"
include "ffn.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "rexrn.mm"
include "mp2b.mm"
include "rexbii.mm"
include "rexcom.mm"
include "bitri.mm"
include "3mix3.mm"
include "sylbir.mm"
include "breq1d.mm"
include "ostth1.mm"
include "3mix1d.mm"
include "syl5bir.mm"
include "pm2.61d.mm"
include "ex.mm"
include "id.mm"
include "cdr.mm"
include "qdrng.mm"
include "qrngbas.mm"
include "abvtriv.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "cres.mm"
include "qabsabv.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "eqcomi.mm"
include "abvcxp.mm"
include "mpan.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "padicabvcxp.mm"
include "ancoms.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "3jaoi.mm"
include "impbii.mm"

theorem ostth
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cQ: class Q
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cK: class K
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
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cN: class N
  let cY: class Y
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )
  assume ostth.k: |- K = ( x e. QQ |-> if ( x = 0 , 0 , 1 ) )

  disjoint a q
  disjoint a x
  disjoint a y
  disjoint q x
  disjoint q y
  disjoint x y
  disjoint a g
  disjoint J a
  disjoint g y
  disjoint J g
  disjoint J y
  disjoint A a
  disjoint A q
  disjoint A x
  disjoint A y
  disjoint Q x
  disjoint Q y
  disjoint F a
  disjoint g q
  disjoint F g
  disjoint F q
  disjoint F y
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
  disjoint q z
  disjoint ph q
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint g p
  disjoint g z
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
  disjoint N x
  disjoint N y
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
  disjoint R a
  disjoint R p
  disjoint R q
  disjoint R y
  disjoint R z
  assert |- ( F e. A <-> ( F = K \/ E. a e. ( 0 (,] 1 ) F = ( y e. QQ |-> ( ( abs ` y ) ^c a ) ) \/ E. a e. RR+ E. g e. ran J F = ( y e. QQ |-> ( ( g ` y ) ^c a ) ) ) )

  proof
    cF
    cA
    wcel
    #
    cF
    cK
    wceq
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
    cc0
    c1
    cioc
    co
    #
    wrex
    #
    cF
    vy
    cq
    @2
    vg
    cv
    #
    cfv
    #
    @4
    ccxp
    co
    #
    cmpt
    #
    wceq
    #
    vg
    cJ
    crn
    wrex
    #
    va
    crp
    wrex
    #
    w3o
    #
    @0
    c1
    vn
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @17
    @0
    @21
    @9
    @17
    @0
    @20
    @9
    vn
    cn
    @0
    @18
    cn
    wcel
    #
    @20
    wa
    #
    wa
    #
    vx
    vy
    cA
    cQ
    @19
    clog
    cfv
    @18
    clog
    cfv
    cdiv
    co
    #
    cF
    cJ
    cK
    @18
    vq
    va
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    @0
    @23
    simpl
    @24
    @18
    c1
    wceq
    #
    wn
    @18
    c2
    cuz
    cfv
    wcel
    #
    @24
    @26
    c1
    c1
    cF
    cfv
    #
    clt
    wbr
    #
    @0
    @29
    wn
    @23
    @0
    @29
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @0
    @28
    c1
    c1
    clt
    @0
    c1
    cc0
    wne
    @28
    c1
    wceq
    ax-1ne0
    cA
    cQ
    c1
    cF
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrng1
    cQ
    qrng.q
    qrng0
    #
    abv1z
    mpan2
    breq2d
    mtbiri
    adantr
    @24
    @20
    @26
    @29
    @0
    @22
    @20
    simprr
    #
    @26
    @19
    @28
    c1
    clt
    @18
    c1
    cF
    fveq2
    breq2d
    syl5ibcom
    mtod
    @24
    @26
    @27
    @24
    @22
    @26
    @27
    wo
    @0
    @22
    @20
    simprl
    @18
    elnn1uz2
    sylib
    ord
    mpd
    @31
    @25
    eqid
    ostth2
    rexlimdvaa
    @9
    @1
    @16
    3mix2
    syl6
    @21
    wn
    @20
    wn
    #
    vn
    cn
    wral
    #
    @0
    @17
    @20
    vn
    cn
    ralnex
    @0
    @33
    @17
    @0
    @33
    wa
    #
    vp
    cv
    #
    cF
    cfv
    #
    c1
    clt
    wbr
    #
    vp
    cprime
    wrex
    #
    @17
    @34
    @38
    cF
    vy
    cq
    @2
    @35
    cJ
    cfv
    #
    cfv
    #
    @4
    ccxp
    co
    #
    cmpt
    #
    wceq
    #
    va
    crp
    wrex
    #
    vp
    cprime
    wrex
    #
    @17
    @34
    @37
    @44
    vp
    cprime
    @34
    @35
    cprime
    wcel
    #
    @37
    @44
    @34
    @46
    @37
    wa
    #
    wa
    #
    vx
    vy
    cA
    @35
    cQ
    @36
    clog
    cfv
    @35
    clog
    cfv
    cdiv
    co
    cneg
    #
    @36
    vz
    cv
    cF
    cfv
    #
    cle
    wbr
    @50
    @36
    cif
    #
    vk
    cF
    cJ
    cK
    vq
    vz
    va
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    @0
    @33
    @47
    simpll
    @48
    @33
    c1
    vk
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    wn
    #
    vk
    cn
    wral
    #
    @0
    @33
    @47
    simplr
    @32
    @55
    vn
    vk
    cn
    vn
    vk
    weq
    #
    @20
    @54
    @57
    @19
    @53
    c1
    clt
    @18
    @52
    cF
    fveq2
    breq2d
    notbid
    cbvralv
    #
    sylib
    @34
    @46
    @37
    simprl
    @34
    @46
    @37
    simprr
    @49
    eqid
    @51
    eqid
    ostth3
    expr
    reximdva
    @45
    @16
    @17
    @16
    @43
    vp
    cprime
    wrex
    #
    va
    crp
    wrex
    #
    @45
    @15
    @59
    va
    crp
    cprime
    cA
    cJ
    wf
    cJ
    cprime
    wfn
    @15
    @59
    wb
    vx
    cA
    cQ
    cJ
    vq
    qrng.q
    qabsabv.a
    padic.j
    padicabvf
    cprime
    cA
    cJ
    ffn
    @14
    @43
    vg
    vp
    cprime
    cJ
    @10
    @39
    wceq
    #
    @13
    @42
    cF
    @61
    vy
    cq
    @12
    @41
    @61
    @11
    @40
    @4
    ccxp
    @2
    @10
    @39
    fveq1
    oveq1d
    mpteq2dv
    eqeq2d
    rexrn
    mp2b
    rexbii
    #
    @43
    va
    vp
    crp
    cprime
    rexcom
    bitri
    @16
    @1
    @9
    3mix3
    sylbir
    syl6
    @38
    wn
    @37
    wn
    #
    vp
    cprime
    wral
    #
    @34
    @17
    @37
    vp
    cprime
    ralnex
    @0
    @33
    @64
    @17
    @0
    @33
    @64
    wa
    #
    wa
    #
    @1
    @9
    @16
    @66
    vx
    cA
    cQ
    vk
    cF
    cJ
    cK
    vq
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    @0
    @65
    simpl
    @66
    @33
    @56
    @0
    @33
    @64
    simprl
    @58
    sylib
    @66
    @64
    @53
    c1
    clt
    wbr
    #
    wn
    #
    vk
    cprime
    wral
    @0
    @33
    @64
    simprr
    @63
    @68
    vp
    vk
    cprime
    vp
    vk
    weq
    #
    @37
    @67
    @69
    @36
    @53
    c1
    clt
    @35
    @52
    cF
    fveq2
    breq1d
    notbid
    cbvralv
    sylib
    ostth1
    3mix1d
    expr
    syl5bir
    pm2.61d
    ex
    syl5bir
    pm2.61d
    @1
    @0
    @9
    @16
    @1
    cF
    cK
    cA
    @1
    id
    cQ
    cdr
    wcel
    cK
    cA
    wcel
    cQ
    qrng.q
    qdrng
    vx
    cA
    cq
    cQ
    cK
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    @30
    ostth.k
    abvtriv
    ax-mp
    syl6eqel
    @7
    @0
    va
    @8
    @4
    @8
    wcel
    #
    @0
    @7
    @6
    cA
    wcel
    #
    cabs
    cq
    cres
    #
    cA
    wcel
    @71
    @72
    cA
    cQ
    qrng.q
    qabsabv.a
    qabsabv
    vy
    cA
    cq
    cQ
    @4
    @73
    @6
    qabsabv.a
    @70
    vy
    cq
    @2
    @73
    cfv
    #
    @4
    ccxp
    co
    #
    cmpt
    @6
    vy
    cq
    @75
    @5
    @2
    cq
    wcel
    @74
    @3
    @4
    ccxp
    @2
    cq
    cabs
    fvres
    oveq1d
    mpteq2ia
    eqcomi
    abvcxp
    mpan
    cF
    @6
    cA
    eleq1
    syl5ibrcom
    rexlimiv
    @16
    @60
    @0
    @62
    @43
    @0
    va
    vp
    crp
    cprime
    @4
    crp
    wcel
    #
    @46
    wa
    @0
    @43
    @42
    cA
    wcel
    #
    @46
    @76
    @77
    vx
    vy
    cA
    @35
    cQ
    @4
    cJ
    vq
    qrng.q
    qabsabv.a
    padic.j
    padicabvcxp
    ancoms
    cF
    @42
    cA
    eleq1
    syl5ibrcom
    rexlimivv
    sylbi
    3jaoi
    impbii
end
