include "crp.mm"
include "cphi.mm"
include "cfv.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "clog.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "cdchr.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "chash.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "adantr.mm"
include "eqid.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "eqeq1i.mm"
include "rabbii.mm"
include "simpr.mm"
include "dchrisum0.mm"
include "imnani.mm"
include "eq0rdv.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "1m0e1.mm"
include "cr.mm"
include "relogcl.mm"
include "adantl.mm"
include "recnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cur.mm"
include "pm2.21i.mm"
include "rpvmasum2.mm"
include "eqeltrrd.mm"

theorem rpvmasum
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cL: class L
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let c.1: class .1.
  let vd: setvar d
  let cC: class C
  let ve: setvar e
  let vr: setvar r
  let cF: class F
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cE: class E
  let cK: class K
  let cG: class G
  let cP: class P
  let wps: wff ps
  let cR: class R
  let cS: class S
  let cB: class B
  let cW: class W
  let cD: class D
  let cM: class M
  let cX: class X
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum.u: |- U = ( Unit ` Z )
  assume rpvmasum.b: |- ( ph -> A e. U )
  assume rpvmasum.t: |- T = ( `' L " { A } )

  disjoint n x
  disjoint A x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint T n
  disjoint T x
  disjoint U n
  disjoint U x
  disjoint Z n
  disjoint Z x
  disjoint L n
  disjoint L x
  disjoint A n
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n u
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint c f
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .1. c
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .1. f
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint .1. i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint .1. j
  disjoint k p
  disjoint k t
  disjoint .1. k
  disjoint m p
  disjoint m t
  disjoint .1. m
  disjoint n p
  disjoint n t
  disjoint .1. n
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint .1. p
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint .1. t
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint c d
  disjoint c e
  disjoint c r
  disjoint c u
  disjoint F c
  disjoint d e
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d p
  disjoint d r
  disjoint d t
  disjoint d u
  disjoint d z
  disjoint F d
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e n
  disjoint e p
  disjoint e r
  disjoint e t
  disjoint e u
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint F e
  disjoint i r
  disjoint i u
  disjoint F i
  disjoint j r
  disjoint j u
  disjoint F j
  disjoint k r
  disjoint F k
  disjoint n r
  disjoint F n
  disjoint p r
  disjoint p u
  disjoint F p
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint I i
  disjoint I k
  disjoint I n
  disjoint I u
  disjoint I x
  disjoint I z
  disjoint J i
  disjoint J k
  disjoint J n
  disjoint J u
  disjoint J x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a p
  disjoint a q
  disjoint a t
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b p
  disjoint b q
  disjoint b t
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c q
  disjoint c v
  disjoint A c
  disjoint d f
  disjoint d q
  disjoint d v
  disjoint A d
  disjoint f q
  disjoint f v
  disjoint A f
  disjoint i q
  disjoint i v
  disjoint A i
  disjoint j q
  disjoint j v
  disjoint A j
  disjoint k q
  disjoint k v
  disjoint A k
  disjoint m q
  disjoint m v
  disjoint A m
  disjoint p q
  disjoint p v
  disjoint A p
  disjoint q t
  disjoint q v
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint t v
  disjoint A t
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint E d
  disjoint E m
  disjoint E x
  disjoint E y
  disjoint K k
  disjoint m r
  disjoint K m
  disjoint K r
  disjoint K y
  disjoint G f
  disjoint N c
  disjoint f r
  disjoint f u
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N m
  disjoint n q
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N q
  disjoint N r
  disjoint N t
  disjoint N u
  disjoint N y
  disjoint N z
  disjoint b n
  disjoint P b
  disjoint P i
  disjoint P k
  disjoint P m
  disjoint n v
  disjoint P n
  disjoint P q
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint c ph
  disjoint d ph
  disjoint e f
  disjoint e m
  disjoint e ph
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph z
  disjoint d ps
  disjoint m ps
  disjoint T d
  disjoint T m
  disjoint T p
  disjoint T r
  disjoint T y
  disjoint R c
  disjoint R d
  disjoint R i
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R u
  disjoint R x
  disjoint R z
  disjoint S c
  disjoint S d
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint U k
  disjoint U m
  disjoint U p
  disjoint U u
  disjoint U z
  disjoint b r
  disjoint B b
  disjoint B c
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B q
  disjoint r v
  disjoint B r
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint W c
  disjoint W f
  disjoint W t
  disjoint W x
  disjoint W z
  disjoint Z f
  disjoint Z k
  disjoint Z m
  disjoint Z p
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint a n
  disjoint a r
  disjoint a u
  disjoint L a
  disjoint b u
  disjoint L b
  disjoint L c
  disjoint L d
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L m
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L v
  disjoint L y
  disjoint L z
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint M u
  disjoint M x
  disjoint M z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( x e. RR+ |-> ( ( ( phi ` N ) x. sum_ n e. ( ( 1 ... ( |_ ` x ) ) i^i T ) ( ( Lam ` n ) / n ) ) - ( log ` x ) ) ) e. O(1) )

  proof
    wph
    vx
    crp
    cN
    cphi
    cfv
    c1
    vx
    cv
    #
    cfl
    cfv
    cfz
    co
    cT
    cin
    vn
    cv
    #
    cvma
    cfv
    @1
    cdiv
    co
    vn
    csu
    cmul
    co
    #
    @0
    clog
    cfv
    #
    c1
    cn
    vm
    cv
    #
    cL
    cfv
    #
    vy
    cv
    #
    cfv
    #
    @4
    cdiv
    co
    #
    vm
    csu
    #
    cc0
    wceq
    #
    vy
    cN
    cdchr
    cfv
    #
    cbs
    cfv
    #
    @11
    c0g
    cfv
    #
    csn
    cdif
    #
    crab
    #
    chash
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    vx
    crp
    @2
    @3
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    crp
    @19
    @20
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @18
    @3
    @2
    cmin
    @22
    @18
    @3
    c1
    cmul
    co
    @3
    @22
    @17
    c1
    @3
    cmul
    wph
    @17
    c1
    wceq
    @21
    wph
    @17
    c1
    cc0
    cmin
    co
    c1
    wph
    @16
    cc0
    c1
    cmin
    wph
    @16
    c0
    chash
    cfv
    cc0
    wph
    @15
    c0
    chash
    wph
    vf
    @15
    wph
    vf
    cv
    #
    @15
    wcel
    #
    wph
    @24
    wa
    #
    vy
    @12
    @13
    vn
    @11
    cL
    cN
    @15
    @23
    cZ
    rpvmasum.z
    rpvmasum.l
    wph
    cN
    cn
    wcel
    @24
    rpvmasum.a
    adantr
    @11
    eqid
    #
    @12
    eqid
    #
    @13
    eqid
    #
    @10
    cn
    @1
    cL
    cfv
    #
    @6
    cfv
    #
    @1
    cdiv
    co
    #
    vn
    csu
    #
    cc0
    wceq
    vy
    @14
    @9
    @32
    cc0
    cn
    @8
    @31
    vm
    vn
    @4
    @1
    wceq
    #
    @7
    @30
    @4
    @1
    cdiv
    @33
    @5
    @29
    @6
    @4
    @1
    cL
    fveq2
    fveq2d
    @33
    id
    oveq12d
    cbvsumv
    eqeq1i
    rabbii
    wph
    @24
    simpr
    dchrisum0
    #
    imnani
    eq0rdv
    fveq2d
    hash0
    syl6eq
    oveq2d
    1m0e1
    syl6eq
    adantr
    oveq2d
    @22
    @3
    @22
    @3
    @21
    @3
    cr
    wcel
    wph
    @0
    relogcl
    adantl
    recnd
    mulid1d
    eqtrd
    oveq2d
    mpteq2dva
    wph
    vx
    vy
    cA
    @12
    cT
    cU
    @13
    vf
    vm
    vn
    @11
    cL
    cN
    @15
    cZ
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    @26
    @27
    @28
    @15
    eqid
    rpvmasum.u
    rpvmasum.b
    rpvmasum.t
    @25
    cA
    cZ
    cur
    cfv
    wceq
    @34
    pm2.21i
    rpvmasum2
    eqeltrrd
end
