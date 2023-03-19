include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cc0.mm"
include "wceq.mm"
include "clog.mm"
include "cif.mm"
include "caddc.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "dchrisumn0.mm"
include "adantr.mm"
include "ifnefalse.mm"
include "syl.mm"
include "oveq2d.mm"
include "fzfid.mm"
include "ad2antrr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "cn.mm"
include "cr.mm"
include "elfznn.mm"
include "vmacl.mm"
include "nndivre.mm"
include "mpancom.mm"
include "recnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "dchrvmasumif.mm"
include "eqeltrrd.mm"

theorem dchrvmasumlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cT: class T
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
  let cR: class R
  let cS: class S
  let cU: class U
  let cB: class B
  let cW: class W
  let cM: class M
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume dchrmusum.g: |- G = ( DChr ` N )
  assume dchrmusum.d: |- D = ( Base ` G )
  assume dchrmusum.1: |- .1. = ( 0g ` G )
  assume dchrmusum.b: |- ( ph -> X e. D )
  assume dchrmusum.n1: |- ( ph -> X =/= .1. )
  assume dchrmusum.f: |- F = ( a e. NN |-> ( ( X ` ( L ` a ) ) / a ) )
  assume dchrmusum.c: |- ( ph -> C e. ( 0 [,) +oo ) )
  assume dchrmusum.t: |- ( ph -> seq 1 ( + , F ) ~~> T )
  assume dchrmusum.2: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( ( seq 1 ( + , F ) ` ( |_ ` y ) ) - T ) ) <_ ( C / y ) )

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
  disjoint T n
  disjoint T x
  disjoint T y
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
  disjoint T p
  disjoint T r
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
  assert |- ( ph -> ( x e. RR+ |-> sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( X ` ( L ` n ) ) x. ( ( Lam ` n ) / n ) ) ) e. O(1) )

  proof
    wph
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cL
    cfv
    cX
    cfv
    #
    @3
    cvma
    cfv
    #
    @3
    cdiv
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cT
    cc0
    wceq
    @0
    clog
    cfv
    #
    cc0
    cif
    #
    caddc
    co
    #
    cmpt
    vx
    crp
    @8
    cmpt
    co1
    wph
    vx
    crp
    @11
    @8
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @11
    @8
    cc0
    caddc
    co
    @8
    @13
    @10
    cc0
    @8
    caddc
    @13
    cT
    cc0
    wne
    #
    @10
    cc0
    wceq
    wph
    @14
    @12
    wph
    vy
    cC
    cD
    cT
    c.1
    cF
    cG
    cL
    cN
    cX
    cZ
    va
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    dchrmusum.g
    dchrmusum.d
    dchrmusum.1
    dchrmusum.b
    dchrmusum.n1
    dchrmusum.f
    dchrmusum.c
    dchrmusum.t
    dchrmusum.2
    dchrisumn0
    adantr
    cT
    cc0
    @9
    cc0
    ifnefalse
    syl
    oveq2d
    @13
    @8
    @13
    @2
    @7
    vn
    @13
    c1
    @1
    fzfid
    @13
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @6
    @16
    @3
    cD
    cG
    cL
    cN
    cX
    cZ
    dchrmusum.g
    rpvmasum.z
    dchrmusum.d
    rpvmasum.l
    wph
    cX
    cD
    wcel
    @12
    @15
    dchrmusum.b
    ad2antrr
    @15
    @3
    cz
    wcel
    @13
    @3
    c1
    @1
    elfzelz
    adantl
    dchrzrhcl
    @16
    @6
    @16
    @3
    cn
    wcel
    #
    @6
    cr
    wcel
    #
    @15
    @17
    @13
    @3
    @1
    elfznn
    adantl
    @5
    cr
    wcel
    @17
    @18
    @3
    vmacl
    @5
    @3
    nndivre
    mpancom
    syl
    recnd
    mulcld
    fsumcl
    addid1d
    eqtrd
    mpteq2dva
    wph
    vx
    vy
    cC
    cD
    cT
    c.1
    vn
    cF
    cG
    cL
    cN
    cX
    cZ
    va
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    dchrmusum.g
    dchrmusum.d
    dchrmusum.1
    dchrmusum.b
    dchrmusum.n1
    dchrmusum.f
    dchrmusum.c
    dchrmusum.t
    dchrmusum.2
    dchrvmasumif
    eqeltrrd
end
