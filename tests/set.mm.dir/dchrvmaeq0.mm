include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "csu.mm"
include "cc0.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wb.mm"
include "wne.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "baib.mm"
include "syl.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wa.mm"
include "adantr.mm"
include "cz.mm"
include "nnz.mm"
include "dchrzrhcl.mm"
include "cc.mm"
include "nncn.mm"
include "nnne0.mm"
include "divcld.mm"
include "isumclim.mm"
include "bitrd.mm"

theorem dchrvmaeq0
  let wph: wff ph
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let c.1: class .1.
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
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
  assume dchrvmaeq0.w: |- W = { y e. ( D \ { .1. } ) | sum_ m e. NN ( ( y ` ( L ` m ) ) / m ) = 0 }

  disjoint F m
  disjoint m y
  disjoint .1. m
  disjoint .1. y
  disjoint C m
  disjoint C y
  disjoint F y
  disjoint a m
  disjoint a y
  disjoint N m
  disjoint N y
  disjoint m ph
  disjoint S m
  disjoint S y
  disjoint Z m
  disjoint Z y
  disjoint D m
  disjoint D y
  disjoint L a
  disjoint L m
  disjoint L y
  disjoint X a
  disjoint X m
  disjoint X y
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
  disjoint m z
  disjoint n u
  disjoint n w
  disjoint n x
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
  disjoint .1. z
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint C n
  disjoint C x
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
  disjoint a p
  disjoint a q
  disjoint a t
  disjoint a v
  disjoint a x
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
  disjoint n q
  disjoint N n
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N q
  disjoint N r
  disjoint N t
  disjoint N u
  disjoint N x
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
  disjoint n ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph x
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
  disjoint S n
  disjoint S r
  disjoint S t
  disjoint S x
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
  disjoint Z n
  disjoint Z p
  disjoint Z x
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D t
  disjoint D x
  disjoint D z
  disjoint a n
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
  disjoint L n
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L v
  disjoint L x
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
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  assert |- ( ph -> ( X e. W <-> S = 0 ) )

  proof
    wph
    cX
    cW
    wcel
    #
    cn
    vm
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    @1
    cdiv
    co
    #
    vm
    csu
    #
    cc0
    wceq
    #
    cS
    cc0
    wceq
    wph
    cX
    cD
    c.1
    csn
    cdif
    #
    wcel
    #
    @0
    @6
    wb
    wph
    cX
    cD
    wcel
    #
    cX
    c.1
    wne
    @8
    dchrisum.b
    dchrisum.n1
    cX
    cD
    c.1
    eldifsn
    sylanbrc
    @0
    @8
    @6
    cn
    @2
    vy
    cv
    #
    cfv
    #
    @1
    cdiv
    co
    #
    vm
    csu
    #
    cc0
    wceq
    @6
    vy
    cX
    @7
    cW
    @10
    cX
    wceq
    #
    @13
    @5
    cc0
    @14
    cn
    @12
    @4
    vm
    @14
    @11
    @3
    @1
    cdiv
    @2
    @10
    cX
    fveq1
    oveq1d
    sumeq2sdv
    eqeq1d
    dchrvmaeq0.w
    elrab2
    baib
    syl
    wph
    @5
    cS
    cc0
    wph
    @4
    cS
    vm
    cF
    c1
    cn
    nnuz
    wph
    1zzd
    @1
    cn
    wcel
    #
    @1
    cF
    cfv
    @4
    wceq
    wph
    va
    @1
    va
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    @16
    cdiv
    co
    @4
    cn
    cF
    @16
    @1
    wceq
    #
    @18
    @3
    @16
    @1
    cdiv
    @19
    @17
    @2
    cX
    @16
    @1
    cL
    fveq2
    fveq2d
    @19
    id
    oveq12d
    dchrvmasumif.f
    @3
    @1
    cdiv
    ovex
    fvmpt
    adantl
    wph
    @15
    wa
    #
    @3
    @1
    @20
    @1
    cD
    cG
    cL
    cN
    cX
    cZ
    rpvmasum.g
    rpvmasum.z
    rpvmasum.d
    rpvmasum.l
    wph
    @9
    @15
    dchrisum.b
    adantr
    @15
    @1
    cz
    wcel
    wph
    @1
    nnz
    adantl
    dchrzrhcl
    @15
    @1
    cc
    wcel
    wph
    @1
    nncn
    adantl
    @15
    @1
    cc0
    wne
    wph
    @1
    nnne0
    adantl
    divcld
    dchrvmasumif.s
    isumclim
    eqeq1d
    bitrd
end
