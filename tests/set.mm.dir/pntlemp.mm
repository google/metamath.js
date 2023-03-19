include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cabs.mm"
include "cle.mm"
include "cicc.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cpnf.mm"
include "cioo.mm"
include "cico.mm"
include "clog.mm"
include "c2.mm"
include "cfl.mm"
include "cfz.mm"
include "csu.mm"
include "cmin.mm"
include "c3.mm"
include "cexp.mm"
include "cc0.mm"
include "wcel.mm"
include "ce.mm"
include "w3a.mm"
include "pntlemc.mm"
include "simp3d.mm"
include "simp1d.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "breq2.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "cr.mm"
include "simpld.mm"
include "rpred.mm"
include "simprd.mm"
include "pntrlog2bnd.mm"
include "reeanv.mm"
include "c4.mm"
include "cdc.mm"
include "adantr.mm"
include "simpl.mm"
include "rpaddcl.mm"
include "syl2an.mm"
include "ltaddrp.mm"
include "jca.mm"
include "adantrr.mm"
include "simprlr.mm"
include "eqid.mm"
include "wss.mm"
include "cxr.mm"
include "rpxr.mm"
include "ad2antrl.mm"
include "rpre.mm"
include "ltaddrp2d.mm"
include "ltled.mm"
include "iooss1.mm"
include "simprrl.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "sylc.mm"
include "simprrr.mm"
include "pntleme.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem pntlemp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let ve: setvar e
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cY: class Y
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vc: setvar c
  let vp: setvar p
  let cC: class C
  let vn: setvar n
  let cT: class T
  assume pntlem3.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntlem3.a: |- ( ph -> A e. RR+ )
  assume pntlem3.A: |- ( ph -> A. x e. RR+ ( abs ` ( ( R ` x ) / x ) ) <_ A )
  assume pntlemp.b: |- ( ph -> B e. RR+ )
  assume pntlemp.l: |- ( ph -> L e. ( 0 (,) 1 ) )
  assume pntlemp.d: |- D = ( A + 1 )
  assume pntlemp.f: |- F = ( ( 1 - ( 1 / D ) ) x. ( ( L / ( ; 3 2 x. B ) ) / ( D ^ 2 ) ) )
  assume pntlemp.K: |- ( ph -> A. e e. ( 0 (,) 1 ) E. x e. RR+ A. k e. ( ( exp ` ( B / e ) ) [,) +oo ) A. y e. ( x (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( L x. e ) ) x. z ) < ( k x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( L x. e ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ e ) )
  assume pntlemp.u: |- ( ph -> U e. RR+ )
  assume pntlemp.u2: |- ( ph -> U <_ A )
  assume pntlemp.e: |- E = ( U / D )
  assume pntlemp.k: |- K = ( exp ` ( B / E ) )
  assume pntlemp.y: |- ( ph -> ( Y e. RR+ /\ 1 <_ Y ) )
  assume pntlemp.U: |- ( ph -> A. z e. ( Y [,) +oo ) ( abs ` ( ( R ` z ) / z ) ) <_ U )

  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint a e
  disjoint a k
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint D a
  disjoint e k
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint D e
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint K e
  disjoint K k
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R e
  disjoint R k
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint E a
  disjoint E e
  disjoint E k
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint Y a
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y y
  disjoint Y z
  disjoint L e
  disjoint L k
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint B e
  disjoint B k
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint U v
  disjoint U w
  disjoint U z
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint p s
  disjoint p u
  disjoint C p
  disjoint s u
  disjoint C s
  disjoint C u
  disjoint c e
  disjoint c k
  disjoint c x
  disjoint K c
  disjoint e t
  disjoint k t
  disjoint K t
  disjoint c n
  disjoint c u
  disjoint R c
  disjoint e n
  disjoint e r
  disjoint e s
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint R n
  disjoint r u
  disjoint R r
  disjoint R s
  disjoint t u
  disjoint R t
  disjoint a c
  disjoint a t
  disjoint E c
  disjoint E t
  disjoint p w
  disjoint p x
  disjoint T p
  disjoint T s
  disjoint T u
  disjoint T w
  disjoint T x
  disjoint a n
  disjoint Y c
  disjoint Y n
  disjoint Y t
  disjoint a r
  disjoint a s
  disjoint L c
  disjoint L t
  disjoint c p
  disjoint c ph
  disjoint p r
  disjoint p t
  disjoint p v
  disjoint p y
  disjoint p ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint U c
  disjoint U t
  assert |- ( ph -> E. w e. RR+ A. v e. ( w [,) +oo ) ( abs ` ( ( R ` v ) / v ) ) <_ ( U - ( F x. ( U ^ 3 ) ) ) )

  proof
    wph
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    c1
    cL
    cE
    cmul
    co
    #
    caddc
    co
    #
    @1
    cmul
    co
    #
    vk
    cv
    @0
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vu
    cv
    #
    cR
    cfv
    @9
    cdiv
    co
    cabs
    cfv
    #
    cE
    cle
    wbr
    #
    vu
    @1
    @5
    cicc
    co
    #
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    vt
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    cK
    cpnf
    cico
    co
    #
    wral
    #
    vt
    crp
    wrex
    #
    @1
    cR
    cfv
    #
    cabs
    cfv
    @1
    clog
    cfv
    #
    cmul
    co
    c2
    @23
    cdiv
    co
    c1
    @1
    cY
    cdiv
    co
    cfl
    cfv
    cfz
    co
    @1
    vn
    cv
    #
    cdiv
    co
    cR
    cfv
    cabs
    cfv
    @24
    clog
    cfv
    cmul
    co
    vn
    csu
    cmul
    co
    cmin
    co
    @1
    cdiv
    co
    vc
    cv
    #
    cle
    wbr
    vz
    c1
    cpnf
    cioo
    co
    wral
    #
    vc
    crp
    wrex
    #
    vv
    cv
    #
    cR
    cfv
    @28
    cdiv
    co
    cabs
    cfv
    cU
    cF
    cU
    c3
    cexp
    co
    cmul
    co
    cmin
    co
    cle
    wbr
    vv
    vw
    cv
    cpnf
    cico
    co
    wral
    vw
    crp
    wrex
    #
    wph
    cE
    cc0
    c1
    cioo
    co
    #
    wcel
    #
    @2
    c1
    cL
    ve
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    cmul
    co
    #
    @6
    clt
    wbr
    #
    wa
    #
    @10
    @32
    cle
    wbr
    #
    vu
    @1
    @35
    cicc
    co
    #
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    vx
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    cB
    @32
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vx
    crp
    wrex
    #
    ve
    @30
    wral
    @21
    wph
    @31
    c1
    cK
    clt
    wbr
    #
    cU
    cE
    cmin
    co
    #
    crp
    wcel
    #
    wph
    cE
    crp
    wcel
    cK
    crp
    wcel
    @31
    @51
    @53
    w3a
    wph
    cA
    cB
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    va
    pntlem3.r
    pntlem3.a
    pntlemp.b
    pntlemp.l
    pntlemp.d
    pntlemp.f
    pntlemp.u
    pntlemp.u2
    pntlemp.e
    pntlemp.k
    pntlemc
    simp3d
    simp1d
    pntlemp.K
    @50
    @21
    ve
    cE
    @30
    @32
    cE
    wceq
    #
    @50
    @15
    vy
    @44
    wral
    #
    vk
    @19
    wral
    #
    vx
    crp
    wrex
    @21
    @54
    @49
    @56
    vx
    crp
    @54
    @45
    @55
    vk
    @48
    @19
    @54
    @47
    cK
    cpnf
    cico
    @54
    @47
    cB
    cE
    cdiv
    co
    #
    ce
    cfv
    cK
    @54
    @46
    @57
    ce
    @32
    cE
    cB
    cdiv
    oveq2
    fveq2d
    pntlemp.k
    syl6eqr
    oveq1d
    @54
    @42
    @15
    vy
    @44
    @54
    @41
    @14
    vz
    crp
    @54
    @37
    @8
    @40
    @13
    @54
    @36
    @7
    @2
    @54
    @35
    @5
    @6
    clt
    @54
    @34
    @4
    @1
    cmul
    @54
    @33
    @3
    c1
    caddc
    @32
    cE
    cL
    cmul
    oveq2
    oveq2d
    oveq1d
    #
    breq1d
    anbi2d
    @54
    @38
    @11
    vu
    @39
    @12
    @54
    @35
    @5
    @1
    cicc
    @58
    oveq2d
    @32
    cE
    @10
    cle
    breq2
    raleqbidv
    anbi12d
    rexbidv
    ralbidv
    raleqbidv
    rexbidv
    @56
    @20
    vx
    vt
    crp
    @43
    @16
    wceq
    #
    @55
    @18
    vk
    @19
    @59
    @15
    vy
    @44
    @17
    @43
    @16
    cpnf
    cioo
    oveq1
    raleqdv
    ralbidv
    cbvrexv
    syl6bb
    rspcva
    syl2anc
    wph
    cY
    cr
    wcel
    #
    c1
    cY
    cle
    wbr
    #
    @27
    wph
    cY
    wph
    cY
    crp
    wcel
    #
    @61
    pntlemp.y
    simpld
    #
    rpred
    #
    wph
    @62
    @61
    pntlemp.y
    simprd
    vz
    cY
    cR
    vn
    va
    vc
    pntlem3.r
    pntrlog2bnd
    syl2anc
    @21
    @27
    wa
    @20
    @26
    wa
    #
    vc
    crp
    wrex
    vt
    crp
    wrex
    wph
    @29
    @20
    @26
    vt
    vc
    crp
    crp
    reeanv
    wph
    @65
    @29
    vt
    vc
    crp
    crp
    wph
    @16
    crp
    wcel
    #
    @25
    crp
    wcel
    #
    wa
    #
    @65
    @29
    wph
    @68
    @65
    wa
    #
    wa
    #
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    @25
    cD
    cR
    cU
    vn
    vk
    cE
    cF
    cK
    cL
    cY
    c4
    @3
    cdiv
    co
    caddc
    co
    c2
    cexp
    co
    cY
    @16
    caddc
    co
    #
    cK
    c2
    cexp
    co
    cmul
    co
    c4
    cexp
    co
    c3
    c2
    cdc
    cB
    cmul
    co
    @52
    cL
    cE
    c2
    cexp
    co
    cmul
    co
    cmul
    co
    cdiv
    co
    cU
    c3
    cmul
    co
    @25
    caddc
    co
    cmul
    co
    ce
    cfv
    caddc
    co
    caddc
    co
    #
    @71
    cY
    va
    pntlem3.r
    wph
    cA
    crp
    wcel
    @69
    pntlem3.a
    adantr
    wph
    cB
    crp
    wcel
    @69
    pntlemp.b
    adantr
    wph
    cL
    @30
    wcel
    @69
    pntlemp.l
    adantr
    pntlemp.d
    pntlemp.f
    wph
    cU
    crp
    wcel
    @69
    pntlemp.u
    adantr
    wph
    cU
    cA
    cle
    wbr
    @69
    pntlemp.u2
    adantr
    pntlemp.e
    pntlemp.k
    wph
    @62
    @61
    wa
    @69
    pntlemp.y
    adantr
    wph
    @68
    @71
    crp
    wcel
    #
    cY
    @71
    clt
    wbr
    #
    wa
    @65
    wph
    @68
    wa
    #
    @73
    @74
    wph
    @62
    @66
    @73
    @68
    @63
    @66
    @67
    simpl
    #
    cY
    @16
    rpaddcl
    syl2an
    #
    wph
    @60
    @66
    @74
    @68
    @64
    @76
    cY
    @16
    ltaddrp
    syl2an
    jca
    adantrr
    wph
    @66
    @67
    @65
    simprlr
    @72
    eqid
    wph
    @22
    @1
    cdiv
    co
    cabs
    cfv
    cU
    cle
    wbr
    vz
    cY
    cpnf
    cico
    co
    wral
    @69
    pntlemp.U
    adantr
    @70
    @71
    cpnf
    cioo
    co
    #
    @17
    wss
    #
    @20
    @15
    vy
    @78
    wral
    #
    vk
    @19
    wral
    wph
    @68
    @79
    @65
    @75
    @16
    cxr
    wcel
    #
    @16
    @71
    cle
    wbr
    @79
    @66
    @81
    wph
    @67
    @16
    rpxr
    ad2antrl
    @75
    @16
    @71
    @66
    @16
    cr
    wcel
    wph
    @67
    @16
    rpre
    ad2antrl
    #
    @75
    @71
    @77
    rpred
    @75
    @16
    cY
    @82
    wph
    @62
    @68
    @63
    adantr
    ltaddrp2d
    ltled
    @16
    @71
    cpnf
    iooss1
    syl2anc
    adantrr
    wph
    @68
    @20
    @26
    simprrl
    @79
    @18
    @80
    vk
    @19
    @15
    vy
    @78
    @17
    ssralv
    ralimdv
    sylc
    wph
    @68
    @20
    @26
    simprrr
    pntleme
    expr
    rexlimdvva
    syl5bir
    mp2and
end
