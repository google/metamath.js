include "cn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "csu.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "adantl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cbs.mm"
include "wf.mm"
include "ad2antrr.mm"
include "cz.mm"
include "cn0.mm"
include "wfo.mm"
include "nnnn0d.mm"
include "eqid.mm"
include "znzrhfo.mm"
include "fof.mm"
include "3syl.mm"
include "adantr.mm"
include "elrabi.mm"
include "nnzd.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ffvelrnd.mm"
include "fsumrecl.mm"
include "cmpt.mm"
include "weq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "sumeq1d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvsumv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fmptd.mm"

theorem dchrisum0ff
  let wph: wff ph
  let vv: setvar v
  let cD: class D
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vq: setvar q
  let vb: setvar b
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let vd: setvar d
  let cC: class C
  let ve: setvar e
  let vr: setvar r
  let cI: class I
  let cJ: class J
  let va: setvar a
  let cA: class A
  let cE: class E
  let cK: class K
  let cP: class P
  let wps: wff ps
  let cT: class T
  let cR: class R
  let cS: class S
  let cU: class U
  let cB: class B
  let cW: class W
  let cM: class M
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum2.g: |- G = ( DChr ` N )
  assume rpvmasum2.d: |- D = ( Base ` G )
  assume rpvmasum2.1: |- .1. = ( 0g ` G )
  assume dchrisum0f.f: |- F = ( b e. NN |-> sum_ v e. { q e. NN | q || b } ( X ` ( L ` v ) ) )
  assume dchrisum0f.x: |- ( ph -> X e. D )
  assume dchrisum0flb.r: |- ( ph -> X : ( Base ` Z ) --> RR )

  disjoint b q
  disjoint b v
  disjoint q v
  disjoint N q
  disjoint L b
  disjoint L v
  disjoint X b
  disjoint X v
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
  disjoint b t
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
  disjoint N n
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N r
  disjoint N t
  disjoint N u
  disjoint N x
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
  disjoint Z n
  disjoint Z p
  disjoint Z x
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
  disjoint L c
  disjoint L d
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L m
  disjoint L n
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L x
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
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> F : NN --> RR )

  proof
    wph
    vn
    cn
    vq
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    vq
    cn
    crab
    #
    vm
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    vm
    csu
    #
    cr
    cF
    wph
    @1
    cn
    wcel
    #
    wa
    #
    @3
    @6
    vm
    @9
    c1
    @1
    cfz
    co
    #
    cfn
    wcel
    @3
    @10
    wss
    #
    @3
    cfn
    wcel
    @9
    c1
    @1
    fzfid
    @8
    @11
    wph
    @1
    vq
    dvdsssfz1
    adantl
    @10
    @3
    ssfi
    syl2anc
    @9
    @4
    @3
    wcel
    #
    wa
    cZ
    cbs
    cfv
    #
    cr
    @5
    cX
    wph
    @13
    cr
    cX
    wf
    @8
    @12
    dchrisum0flb.r
    ad2antrr
    @9
    cz
    @13
    cL
    wf
    #
    @4
    cz
    wcel
    @5
    @13
    wcel
    @12
    wph
    @14
    @8
    wph
    cN
    cn0
    wcel
    cz
    @13
    cL
    wfo
    @14
    wph
    cN
    rpvmasum.a
    nnnn0d
    @13
    cL
    cN
    cZ
    rpvmasum.z
    @13
    eqid
    rpvmasum.l
    znzrhfo
    cz
    @13
    cL
    fof
    3syl
    adantr
    @12
    @4
    @2
    vq
    @4
    cn
    elrabi
    nnzd
    cz
    @13
    @4
    cL
    ffvelrn
    syl2an
    ffvelrnd
    fsumrecl
    cF
    vb
    cn
    @0
    vb
    cv
    #
    cdvds
    wbr
    #
    vq
    cn
    crab
    #
    vv
    cv
    #
    cL
    cfv
    #
    cX
    cfv
    #
    vv
    csu
    #
    cmpt
    vn
    cn
    @7
    cmpt
    dchrisum0f.f
    vb
    vn
    cn
    @21
    @7
    vb
    vn
    weq
    #
    @21
    @3
    @20
    vv
    csu
    @7
    @22
    @17
    @3
    @20
    vv
    @22
    @16
    @2
    vq
    cn
    @15
    @1
    @0
    cdvds
    breq2
    rabbidv
    sumeq1d
    @3
    @20
    @6
    vv
    vm
    vv
    vm
    weq
    @19
    @5
    cX
    @18
    @4
    cL
    fveq2
    fveq2d
    cbvsumv
    syl6eq
    cbvmptv
    eqtri
    fmptd
end
