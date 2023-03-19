include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "clog.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cfl.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "c3.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "wrex.mm"
include "wex.mm"
include "crp.mm"
include "cfz.mm"
include "cvma.mm"
include "csu.mm"
include "wceq.mm"
include "cif.mm"
include "co1.mm"
include "wcel.mm"
include "eqid.mm"
include "dchrvmasumlema.mm"
include "adantr.mm"
include "wne.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "dchrvmasumiflem2.mm"
include "rexlimdvaa.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem dchrvmasumif
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let c.1: class .1.
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vm: setvar m
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let vd: setvar d
  let ve: setvar e
  let vr: setvar r
  let cI: class I
  let cJ: class J
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cA: class A
  let cE: class E
  let cK: class K
  let cP: class P
  let wps: wff ps
  let cT: class T
  let cR: class R
  let cU: class U
  let cB: class B
  let cW: class W
  let cM: class M
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum.g: |- G = ( DChr ` N )
  assume rpvmasum.d: |- D = ( Base ` G )
  assume rpvmasum.1: |- .1. = ( 0g ` G )
  assume dchrisum.b: |- ( ph -> X e. D )
  assume dchrisum.n1: |- ( ph -> X =/= .1. )
  assume dchrvmasumif.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) / a ) )
  assume dchrvmasumif.c: |- ( ph -> C e. ( 0 [,) +oo ) )
  assume dchrvmasumif.s: |- ( ph -> seq 1 ( + , F ) ~~> S )
  assume dchrvmasumif.1: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - S ) ) <_ ( C / y ) )

  disjoint n x
  disjoint n y
  disjoint x y
  disjoint .1. n
  disjoint .1. x
  disjoint .1. y
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint a x
  disjoint a y
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint n ph
  disjoint ph x
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint a n
  disjoint L a
  disjoint L n
  disjoint L x
  disjoint L y
  disjoint X a
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint F m
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
  disjoint n z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
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
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint .1. p
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint .1. t
  disjoint .1. z
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C m
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
  disjoint A x
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
  disjoint T n
  disjoint T p
  disjoint T r
  disjoint T x
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
  disjoint S r
  disjoint S t
  disjoint U k
  disjoint U m
  disjoint U n
  disjoint U p
  disjoint U u
  disjoint U x
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
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D t
  disjoint D z
  disjoint a r
  disjoint a u
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
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( ph -> ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( X ` ( L ` n ) ) x. ( ( Lam ` n ) / n ) ) + if ( S = 0 , ( log ` x ) , 0 ) ) ) e. O(1) )

  proof
    wph
    caddc
    va
    cn
    va
    cv
    #
    cL
    cfv
    cX
    cfv
    @0
    clog
    cfv
    @0
    cdiv
    co
    cmul
    co
    cmpt
    #
    c1
    cseq
    #
    vt
    cv
    #
    cli
    wbr
    #
    vy
    cv
    #
    cfl
    cfv
    #
    @2
    cfv
    @3
    cmin
    co
    cabs
    cfv
    vc
    cv
    #
    @5
    clog
    cfv
    @5
    cdiv
    co
    cmul
    co
    cle
    wbr
    vy
    c3
    cpnf
    cico
    co
    wral
    #
    wa
    #
    vc
    cc0
    cpnf
    cico
    co
    #
    wrex
    #
    vt
    wex
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    cfz
    co
    vn
    cv
    #
    cL
    cfv
    cX
    cfv
    @13
    cvma
    cfv
    @13
    cdiv
    co
    cmul
    co
    vn
    csu
    cS
    cc0
    wceq
    @12
    clog
    cfv
    cc0
    cif
    caddc
    co
    cmpt
    co1
    wcel
    #
    wph
    vy
    vt
    cD
    c.1
    @1
    cG
    cL
    cN
    cX
    cZ
    va
    vc
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    @1
    eqid
    #
    dchrvmasumlema
    wph
    @11
    @14
    vt
    wph
    @9
    @14
    vc
    @10
    wph
    @7
    @10
    wcel
    #
    @9
    wa
    #
    wa
    vx
    vy
    cC
    cD
    cS
    @3
    c.1
    vn
    @7
    cF
    cG
    @1
    cL
    cN
    cX
    cZ
    va
    rpvmasum.z
    rpvmasum.l
    wph
    cN
    cn
    wcel
    @17
    rpvmasum.a
    adantr
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    wph
    cX
    cD
    wcel
    @17
    dchrisum.b
    adantr
    wph
    cX
    c.1
    wne
    @17
    dchrisum.n1
    adantr
    dchrvmasumif.f
    wph
    cC
    @10
    wcel
    @17
    dchrvmasumif.c
    adantr
    wph
    caddc
    cF
    c1
    cseq
    #
    cS
    cli
    wbr
    @17
    dchrvmasumif.s
    adantr
    wph
    @6
    @18
    cfv
    cS
    cmin
    co
    cabs
    cfv
    cC
    @5
    cdiv
    co
    cle
    wbr
    vy
    c1
    cpnf
    cico
    co
    wral
    @17
    dchrvmasumif.1
    adantr
    @15
    wph
    @16
    @9
    simprl
    wph
    @16
    @4
    @8
    simprrl
    wph
    @16
    @4
    @8
    simprrr
    dchrvmasumiflem2
    rexlimdvaa
    exlimdv
    mpd
end
