include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "clog.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "cmu.mm"
include "wceq.mm"
include "wa.mm"
include "fzfid.mm"
include "wcel.mm"
include "adantr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "cn.mm"
include "cr.mm"
include "elfznn.mm"
include "mucl.mm"
include "zred.mm"
include "nndivre.mm"
include "mpancom.mm"
include "syl.mm"
include "recnd.mm"
include "mulcld.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nndivred.mm"
include "fsumcl.mm"
include "crp.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "rpdivcld.mm"
include "fsumadd.mm"
include "cmin.mm"
include "relogdivd.mm"
include "oveq2d.mm"
include "cc.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "eqtrd.mm"
include "adddid.mm"
include "sumeq2dv.mm"
include "dchrvmasumlem1.mm"
include "dchrvmasum2lem.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "sumeq2sdv.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "vmacl.mm"
include "addid1d.mm"
include "iffalse.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "pm2.61dan.mm"

theorem dchrvmasum2if
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cD: class D
  let c.1: class .1.
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vk: setvar k
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
  let cP: class P
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
  assume rpvmasum.g: |- G = ( DChr ` N )
  assume rpvmasum.d: |- D = ( Base ` G )
  assume rpvmasum.1: |- .1. = ( 0g ` G )
  assume dchrisum.b: |- ( ph -> X e. D )
  assume dchrisum.n1: |- ( ph -> X =/= .1. )
  assume dchrvmasum.a: |- ( ph -> A e. RR+ )
  assume dchrvmasum2.2: |- ( ph -> 1 <_ A )

  disjoint A n
  disjoint m n
  disjoint .1. m
  disjoint .1. n
  disjoint d m
  disjoint d n
  disjoint A d
  disjoint A m
  disjoint N m
  disjoint N n
  disjoint d ph
  disjoint m ph
  disjoint n ph
  disjoint d ps
  disjoint m ps
  disjoint Z m
  disjoint Z n
  disjoint D m
  disjoint D n
  disjoint L d
  disjoint L m
  disjoint L n
  disjoint X d
  disjoint X m
  disjoint X n
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
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
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
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
  disjoint N p
  disjoint q r
  disjoint q u
  disjoint N q
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
  disjoint e f
  disjoint e m
  disjoint e ph
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint p ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph x
  disjoint ph z
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
  disjoint Z p
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
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
  disjoint L f
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L p
  disjoint L r
  disjoint L t
  disjoint u v
  disjoint L u
  disjoint L v
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
  disjoint X b
  disjoint X c
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( sum_ n e. ( 1 ... ( |_ ` A ) ) ( ( X ` ( L ` n ) ) x. ( ( Lam ` n ) / n ) ) + if ( ps , ( log ` A ) , 0 ) ) = sum_ d e. ( 1 ... ( |_ ` A ) ) ( ( ( X ` ( L ` d ) ) x. ( ( mmu ` d ) / d ) ) x. sum_ m e. ( 1 ... ( |_ ` ( A / d ) ) ) ( ( X ` ( L ` m ) ) x. ( ( log ` if ( ps , ( A / d ) , m ) ) / m ) ) ) )

  proof
    wph
    wps
    c1
    cA
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
    @2
    cvma
    cfv
    #
    @2
    cdiv
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    wps
    cA
    clog
    cfv
    #
    cc0
    cif
    #
    caddc
    co
    #
    @1
    vd
    cv
    #
    cL
    cfv
    cX
    cfv
    #
    @11
    cmu
    cfv
    #
    @11
    cdiv
    co
    #
    cmul
    co
    #
    c1
    cA
    @11
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vm
    cv
    #
    cL
    cfv
    cX
    cfv
    #
    wps
    @16
    @19
    cif
    #
    clog
    cfv
    #
    @19
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmul
    co
    #
    vd
    csu
    #
    wceq
    wph
    wps
    wa
    @7
    @8
    caddc
    co
    #
    @1
    @15
    @18
    @20
    @16
    clog
    cfv
    #
    @19
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmul
    co
    #
    vd
    csu
    #
    @10
    @27
    wph
    @28
    @34
    wceq
    wps
    wph
    @1
    @15
    @18
    @20
    @19
    clog
    cfv
    #
    @19
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmul
    co
    #
    @15
    @18
    @20
    @16
    @19
    cdiv
    co
    #
    clog
    cfv
    #
    @19
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmul
    co
    #
    caddc
    co
    #
    vd
    csu
    @1
    @39
    vd
    csu
    #
    @1
    @45
    vd
    csu
    #
    caddc
    co
    @34
    @28
    wph
    @1
    @39
    @45
    vd
    wph
    c1
    @0
    fzfid
    #
    wph
    @11
    @1
    wcel
    #
    wa
    #
    @15
    @38
    @51
    @12
    @14
    @51
    @11
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
    cX
    cD
    wcel
    #
    @50
    dchrisum.b
    adantr
    #
    @50
    @11
    cz
    wcel
    wph
    @11
    c1
    @0
    elfzelz
    adantl
    dchrzrhcl
    @51
    @14
    @51
    @11
    cn
    wcel
    #
    @14
    cr
    wcel
    #
    @50
    @54
    wph
    @11
    @0
    elfznn
    #
    adantl
    @13
    cr
    wcel
    @54
    @55
    @54
    @13
    @11
    mucl
    zred
    @13
    @11
    nndivre
    mpancom
    syl
    recnd
    mulcld
    #
    @51
    @18
    @37
    vm
    @51
    c1
    @17
    fzfid
    #
    @51
    @19
    @18
    wcel
    #
    wa
    #
    @20
    @36
    @60
    @19
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
    @51
    @52
    @59
    @53
    adantr
    @59
    @19
    cz
    wcel
    @51
    @19
    c1
    @17
    elfzelz
    adantl
    dchrzrhcl
    #
    @60
    @36
    @60
    @35
    @19
    @60
    @19
    @60
    @19
    @59
    @19
    cn
    wcel
    @51
    @19
    @17
    elfznn
    adantl
    #
    nnrpd
    #
    relogcld
    #
    @62
    nndivred
    recnd
    #
    mulcld
    #
    fsumcl
    #
    mulcld
    @51
    @15
    @44
    @57
    @51
    @18
    @43
    vm
    @58
    @60
    @20
    @42
    @61
    @60
    @42
    @60
    @41
    @19
    @60
    @40
    @60
    @16
    @19
    @51
    @16
    crp
    wcel
    #
    @59
    wph
    cA
    crp
    wcel
    @11
    crp
    wcel
    @68
    @50
    dchrvmasum.a
    @50
    @11
    @56
    nnrpd
    cA
    @11
    rpdivcl
    syl2an
    #
    adantr
    #
    @63
    rpdivcld
    relogcld
    #
    @62
    nndivred
    recnd
    #
    mulcld
    #
    fsumcl
    #
    mulcld
    fsumadd
    wph
    @1
    @33
    @46
    vd
    @51
    @33
    @15
    @38
    @44
    caddc
    co
    #
    cmul
    co
    @46
    @51
    @32
    @75
    @15
    cmul
    @51
    @32
    @18
    @37
    @43
    caddc
    co
    #
    vm
    csu
    @75
    @51
    @18
    @31
    @76
    vm
    @60
    @31
    @20
    @36
    @42
    caddc
    co
    #
    cmul
    co
    @76
    @60
    @30
    @77
    @20
    cmul
    @60
    @30
    @35
    @41
    caddc
    co
    #
    @19
    cdiv
    co
    @77
    @60
    @29
    @78
    @19
    cdiv
    @60
    @78
    @35
    @29
    @35
    cmin
    co
    #
    caddc
    co
    @29
    @60
    @41
    @79
    @35
    caddc
    @60
    @16
    @19
    @70
    @63
    relogdivd
    oveq2d
    @60
    @35
    @29
    @60
    @35
    @64
    recnd
    #
    @51
    @29
    cc
    wcel
    @59
    @51
    @29
    @51
    @16
    @69
    relogcld
    recnd
    adantr
    pncan3d
    eqtr2d
    oveq1d
    @60
    @35
    @41
    @19
    @80
    @60
    @41
    @71
    recnd
    @60
    @19
    @62
    nncnd
    @60
    @19
    @62
    nnne0d
    divdird
    eqtrd
    oveq2d
    @60
    @20
    @36
    @42
    @61
    @65
    @72
    adddid
    eqtrd
    sumeq2dv
    @51
    @18
    @37
    @43
    vm
    @58
    @66
    @73
    fsumadd
    eqtrd
    oveq2d
    @51
    @15
    @38
    @44
    @57
    @67
    @74
    adddid
    eqtrd
    sumeq2dv
    wph
    @7
    @47
    @8
    @48
    caddc
    wph
    cA
    cD
    c.1
    vm
    vn
    cG
    cL
    cN
    cX
    cZ
    vd
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    dchrvmasum.a
    dchrvmasumlem1
    #
    wph
    cA
    cD
    c.1
    vm
    cG
    cL
    cN
    cX
    cZ
    vd
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.g
    rpvmasum.d
    rpvmasum.1
    dchrisum.b
    dchrisum.n1
    dchrvmasum.a
    dchrvmasum2.2
    dchrvmasum2lem
    oveq12d
    3eqtr4rd
    adantr
    wps
    @10
    @28
    wceq
    wph
    wps
    @9
    @8
    @7
    caddc
    wps
    @8
    cc0
    iftrue
    oveq2d
    adantl
    wps
    @27
    @34
    wceq
    wph
    wps
    @1
    @26
    @33
    vd
    wps
    @25
    @32
    @15
    cmul
    wps
    @18
    @24
    @31
    vm
    wps
    @23
    @30
    @20
    cmul
    wps
    @22
    @29
    @19
    cdiv
    wps
    @21
    @16
    clog
    wps
    @16
    @19
    iftrue
    fveq2d
    oveq1d
    oveq2d
    sumeq2sdv
    oveq2d
    sumeq2sdv
    adantl
    3eqtr4d
    wph
    wps
    wn
    #
    wa
    #
    @7
    cc0
    caddc
    co
    @7
    @10
    @27
    @83
    @7
    wph
    @7
    cc
    wcel
    @82
    wph
    @1
    @6
    vn
    @49
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @5
    @85
    @2
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
    @52
    @84
    dchrisum.b
    adantr
    @84
    @2
    cz
    wcel
    wph
    @2
    c1
    @0
    elfzelz
    adantl
    dchrzrhcl
    @85
    @2
    cn
    wcel
    #
    @5
    cc
    wcel
    @84
    @86
    wph
    @2
    @0
    elfznn
    adantl
    @86
    @5
    @4
    cr
    wcel
    @86
    @5
    cr
    wcel
    @2
    vmacl
    @4
    @2
    nndivre
    mpancom
    recnd
    syl
    mulcld
    fsumcl
    adantr
    addid1d
    @83
    @9
    cc0
    @7
    caddc
    @82
    @9
    cc0
    wceq
    wph
    wps
    @8
    cc0
    iffalse
    adantl
    oveq2d
    @82
    wph
    @27
    @47
    @7
    @82
    @1
    @26
    @39
    vd
    @82
    @25
    @38
    @15
    cmul
    @82
    @18
    @24
    @37
    vm
    @82
    @23
    @36
    @20
    cmul
    @82
    @22
    @35
    @19
    cdiv
    @82
    @21
    @19
    clog
    wps
    @16
    @19
    iffalse
    fveq2d
    oveq1d
    oveq2d
    sumeq2sdv
    oveq2d
    sumeq2sdv
    wph
    @7
    @47
    @81
    eqcomd
    sylan9eqr
    3eqtr4d
    pm2.61dan
end
