include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "c3.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "wrex.mm"
include "pntlema.mm"
include "wa.mm"
include "clog.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "c2.mm"
include "adantr.mm"
include "cc0.mm"
include "cioo.mm"
include "clt.mm"
include "simpr.mm"
include "eqid.mm"
include "cicc.mm"
include "cxr.mm"
include "w3a.mm"
include "pntlemc.mm"
include "simp2d.mm"
include "rpxrd.mm"
include "pnfxr.mm"
include "a1i.mm"
include "cr.mm"
include "rpred.mm"
include "ltpnf.mm"
include "syl.mm"
include "lbico1.mm"
include "syl3anc.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "cfz.mm"
include "csu.mm"
include "pntlemo.mm"
include "ralrimiva.mm"
include "raleqdv.mm"
include "rspcev.mm"

theorem pntleme
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vx: setvar x
  let cI: class I
  let vn: setvar n
  let cJ: class J
  let vj: setvar j
  let vm: setvar m
  let cM: class M
  let cO: class O
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vl: setvar l
  let cV: class V
  let cZ: class Z
  assume pntlem1.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntlem1.a: |- ( ph -> A e. RR+ )
  assume pntlem1.b: |- ( ph -> B e. RR+ )
  assume pntlem1.l: |- ( ph -> L e. ( 0 (,) 1 ) )
  assume pntlem1.d: |- D = ( A + 1 )
  assume pntlem1.f: |- F = ( ( 1 - ( 1 / D ) ) x. ( ( L / ( ; 3 2 x. B ) ) / ( D ^ 2 ) ) )
  assume pntlem1.u: |- ( ph -> U e. RR+ )
  assume pntlem1.u2: |- ( ph -> U <_ A )
  assume pntlem1.e: |- E = ( U / D )
  assume pntlem1.k: |- K = ( exp ` ( B / E ) )
  assume pntlem1.y: |- ( ph -> ( Y e. RR+ /\ 1 <_ Y ) )
  assume pntlem1.x: |- ( ph -> ( X e. RR+ /\ Y < X ) )
  assume pntlem1.c: |- ( ph -> C e. RR+ )
  assume pntlem1.w: |- W = ( ( ( Y + ( 4 / ( L x. E ) ) ) ^ 2 ) + ( ( ( X x. ( K ^ 2 ) ) ^ 4 ) + ( exp ` ( ( ( ; 3 2 x. B ) / ( ( U - E ) x. ( L x. ( E ^ 2 ) ) ) ) x. ( ( U x. 3 ) + C ) ) ) ) )
  assume pntleme.U: |- ( ph -> A. z e. ( Y [,) +oo ) ( abs ` ( ( R ` z ) / z ) ) <_ U )
  assume pntleme.K: |- ( ph -> A. k e. ( K [,) +oo ) A. y e. ( X (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( L x. E ) ) x. z ) < ( k x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( L x. E ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ E ) )
  assume pntleme.C: |- ( ph -> A. z e. ( 1 (,) +oo ) ( ( ( ( abs ` ( R ` z ) ) x. ( log ` z ) ) - ( ( 2 / ( log ` z ) ) x. sum_ i e. ( 1 ... ( |_ ` ( z / Y ) ) ) ( ( abs ` ( R ` ( z / i ) ) ) x. ( log ` i ) ) ) ) / z ) <_ C )

  disjoint C z
  disjoint F w
  disjoint y z
  disjoint k u
  disjoint k y
  disjoint k z
  disjoint L k
  disjoint u y
  disjoint u z
  disjoint L u
  disjoint L y
  disjoint L z
  disjoint K k
  disjoint K y
  disjoint K z
  disjoint ph v
  disjoint i k
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint k v
  disjoint k w
  disjoint R k
  disjoint u v
  disjoint u w
  disjoint R u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint U w
  disjoint U z
  disjoint W v
  disjoint W w
  disjoint W z
  disjoint X k
  disjoint X y
  disjoint X z
  disjoint Y i
  disjoint Y z
  disjoint a k
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint E a
  disjoint E k
  disjoint E u
  disjoint E v
  disjoint E y
  disjoint E z
  disjoint x z
  disjoint C x
  disjoint I n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint L j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint L m
  disjoint n u
  disjoint L n
  disjoint u x
  disjoint L x
  disjoint K j
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M z
  disjoint O n
  disjoint O x
  disjoint O z
  disjoint j v
  disjoint j ph
  disjoint m v
  disjoint m ph
  disjoint n v
  disjoint n ph
  disjoint v x
  disjoint ph x
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N z
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b m
  disjoint b n
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint e f
  disjoint e g
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e m
  disjoint e n
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint R e
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g l
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint i j
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint j l
  disjoint j w
  disjoint R j
  disjoint k l
  disjoint l m
  disjoint l n
  disjoint l u
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint R l
  disjoint m w
  disjoint R m
  disjoint n w
  disjoint R n
  disjoint w x
  disjoint R x
  disjoint V n
  disjoint V u
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U x
  disjoint W n
  disjoint X n
  disjoint Y j
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint a e
  disjoint a g
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint E e
  disjoint E g
  disjoint E j
  disjoint E m
  disjoint E n
  disjoint E x
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z u
  disjoint Z x
  disjoint Z z
  assert |- ( ph -> E. w e. RR+ A. v e. ( w [,) +oo ) ( abs ` ( ( R ` v ) / v ) ) <_ ( U - ( F x. ( U ^ 3 ) ) ) )

  proof
    wph
    cW
    crp
    wcel
    vv
    cv
    #
    cR
    cfv
    @0
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
    #
    vv
    cW
    cpnf
    cico
    co
    #
    wral
    #
    @1
    vv
    vw
    cv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vw
    crp
    wrex
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    cW
    cX
    cY
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlem1.y
    pntlem1.x
    pntlem1.c
    pntlem1.w
    pntlema
    wph
    @1
    vv
    @2
    wph
    @0
    @2
    wcel
    #
    wa
    vy
    vz
    vu
    cA
    cB
    cC
    cD
    cR
    cU
    vi
    cE
    cF
    cK
    cL
    cX
    clog
    cfv
    cK
    clog
    cfv
    #
    cdiv
    co
    cfl
    cfv
    c1
    caddc
    co
    #
    @0
    clog
    cfv
    @8
    cdiv
    co
    c2
    cdiv
    co
    cfl
    cfv
    #
    cW
    cX
    cY
    @0
    va
    pntlem1.r
    wph
    cA
    crp
    wcel
    @7
    pntlem1.a
    adantr
    wph
    cB
    crp
    wcel
    @7
    pntlem1.b
    adantr
    wph
    cL
    cc0
    c1
    cioo
    co
    #
    wcel
    @7
    pntlem1.l
    adantr
    pntlem1.d
    pntlem1.f
    wph
    cU
    crp
    wcel
    @7
    pntlem1.u
    adantr
    wph
    cU
    cA
    cle
    wbr
    @7
    pntlem1.u2
    adantr
    pntlem1.e
    pntlem1.k
    wph
    cY
    crp
    wcel
    c1
    cY
    cle
    wbr
    wa
    @7
    pntlem1.y
    adantr
    wph
    cX
    crp
    wcel
    cY
    cX
    clt
    wbr
    wa
    @7
    pntlem1.x
    adantr
    wph
    cC
    crp
    wcel
    @7
    pntlem1.c
    adantr
    pntlem1.w
    wph
    @7
    simpr
    @9
    eqid
    @10
    eqid
    wph
    vz
    cv
    #
    cR
    cfv
    #
    @12
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
    @7
    pntleme.U
    adantr
    wph
    vy
    cv
    #
    @12
    clt
    wbr
    #
    c1
    cL
    cE
    cmul
    co
    caddc
    co
    @12
    cmul
    co
    #
    cK
    @14
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
    @20
    cdiv
    co
    cabs
    cfv
    cE
    cle
    wbr
    vu
    @12
    @16
    cicc
    co
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    cX
    cpnf
    cioo
    co
    #
    wral
    #
    @7
    wph
    cK
    cK
    cpnf
    cico
    co
    #
    wcel
    #
    @15
    @16
    vk
    cv
    #
    @14
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    @21
    wa
    #
    vz
    crp
    wrex
    #
    vy
    @24
    wral
    #
    vk
    @26
    wral
    @25
    wph
    cK
    cxr
    wcel
    cpnf
    cxr
    wcel
    #
    cK
    cpnf
    clt
    wbr
    #
    @27
    wph
    cK
    wph
    cE
    crp
    wcel
    cK
    crp
    wcel
    cE
    @11
    wcel
    c1
    cK
    clt
    wbr
    cU
    cE
    cmin
    co
    crp
    wcel
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
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlemc
    simp2d
    #
    rpxrd
    @35
    wph
    pnfxr
    a1i
    wph
    cK
    cr
    wcel
    @36
    wph
    cK
    @37
    rpred
    cK
    ltpnf
    syl
    cK
    cpnf
    lbico1
    syl3anc
    pntleme.K
    @34
    @25
    vk
    cK
    @26
    @28
    cK
    wceq
    #
    @33
    @23
    vy
    @24
    @38
    @32
    @22
    vz
    crp
    @38
    @31
    @19
    @21
    @38
    @30
    @18
    @15
    @38
    @29
    @17
    @16
    clt
    @28
    cK
    @14
    cmul
    oveq1
    breq2d
    anbi2d
    anbi1d
    rexbidv
    ralbidv
    rspcva
    syl2anc
    adantr
    wph
    @13
    cabs
    cfv
    @12
    clog
    cfv
    #
    cmul
    co
    c2
    @39
    cdiv
    co
    c1
    @12
    cY
    cdiv
    co
    cfl
    cfv
    cfz
    co
    @12
    vi
    cv
    #
    cdiv
    co
    cR
    cfv
    cabs
    cfv
    @40
    clog
    cfv
    cmul
    co
    vi
    csu
    cmul
    co
    cmin
    co
    @12
    cdiv
    co
    cC
    cle
    wbr
    vz
    c1
    cpnf
    cioo
    co
    wral
    @7
    pntleme.C
    adantr
    pntlemo
    ralrimiva
    @6
    @3
    vw
    cW
    crp
    @4
    cW
    wceq
    @1
    vv
    @5
    @2
    @4
    cW
    cpnf
    cico
    oveq1
    raleqdv
    rspcev
    syl2anc
end
