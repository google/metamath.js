include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cmu.mm"
include "cdiv.mm"
include "clog.mm"
include "cmul.mm"
include "csu.mm"
include "cvma.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "rpred.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "adantrr.mm"
include "elrabi.mm"
include "ad2antll.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "elfznn.mm"
include "ad2antrl.mm"
include "nndivred.mm"
include "recnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "mulcld.mm"
include "dvdsflsumcom.mm"
include "cmpt.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "vmaf.mm"
include "a1i.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "vmasum.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "muinv.mm"
include "fveq1d.mm"
include "cvv.mm"
include "sumex.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "sylan9eq.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "wb.mm"
include "nndivdvds.mm"
include "syl2an.mm"
include "mpbid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cfn.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "nncnd.mm"
include "zcnd.mm"
include "anassrs.mm"
include "nnne0d.mm"
include "fsumdivc.mm"
include "cc0.mm"
include "wne.mm"
include "div23d.mm"
include "3eqtrd.mm"
include "fsummulc2.mm"
include "cle.mm"
include "fznnfl.mm"
include "simprbda.mm"
include "ad2antrr.mm"
include "mul4d.mm"
include "ad2antlr.mm"
include "dchrzrhmul.mm"
include "crp.mm"
include "rpmulcld.mm"
include "rpcnne0d.mm"
include "div23.mm"
include "syl3anc.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan3d.mm"
include "3eqtr4rd.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem dchrvmasumlem1
  let wph: wff ph
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
  assume rpvmasum.g: |- G = ( DChr ` N )
  assume rpvmasum.d: |- D = ( Base ` G )
  assume rpvmasum.1: |- .1. = ( 0g ` G )
  assume dchrisum.b: |- ( ph -> X e. D )
  assume dchrisum.n1: |- ( ph -> X =/= .1. )
  assume dchrvmasum.a: |- ( ph -> A e. RR+ )

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
  assert |- ( ph -> sum_ n e. ( 1 ... ( |_ ` A ) ) ( ( X ` ( L ` n ) ) x. ( ( Lam ` n ) / n ) ) = sum_ d e. ( 1 ... ( |_ ` A ) ) ( ( ( X ` ( L ` d ) ) x. ( ( mmu ` d ) / d ) ) x. sum_ m e. ( 1 ... ( |_ ` ( A / d ) ) ) ( ( X ` ( L ` m ) ) x. ( ( log ` m ) / m ) ) ) )

  proof
    wph
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vx
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @3
    cL
    cfv
    #
    cX
    cfv
    #
    vd
    cv
    #
    cmu
    cfv
    #
    @3
    cdiv
    co
    #
    @3
    @8
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vd
    csu
    #
    vn
    csu
    @1
    c1
    cA
    @8
    cdiv
    co
    cfl
    cfv
    #
    cfz
    co
    #
    @8
    vm
    cv
    #
    cmul
    co
    #
    cL
    cfv
    #
    cX
    cfv
    #
    @9
    @19
    cdiv
    co
    #
    @19
    @8
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    vd
    csu
    @1
    @7
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
    @1
    @8
    cL
    cfv
    cX
    cfv
    #
    @9
    @8
    cdiv
    co
    #
    cmul
    co
    #
    @17
    @18
    cL
    cfv
    cX
    cfv
    #
    @18
    clog
    cfv
    #
    @18
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    cmul
    co
    #
    vd
    csu
    wph
    vx
    cA
    @14
    @26
    vm
    vn
    vd
    @3
    @19
    wceq
    #
    @7
    @21
    @13
    @25
    cmul
    @39
    @6
    @20
    cX
    @3
    @19
    cL
    fveq2
    fveq2d
    @39
    @10
    @22
    @12
    @24
    cmul
    @3
    @19
    @9
    cdiv
    oveq2
    @39
    @11
    @23
    clog
    @3
    @19
    @8
    cdiv
    oveq1
    fveq2d
    oveq12d
    oveq12d
    wph
    cA
    dchrvmasum.a
    rpred
    #
    wph
    @3
    @1
    wcel
    #
    @8
    @5
    wcel
    #
    wa
    wa
    #
    @7
    @13
    wph
    @41
    @7
    cc
    wcel
    @42
    wph
    @41
    wa
    #
    @3
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
    @41
    dchrisum.b
    adantr
    @41
    @3
    cz
    wcel
    wph
    @3
    c1
    @0
    elfzelz
    adantl
    dchrzrhcl
    #
    adantrr
    @43
    @10
    @12
    @43
    @10
    @43
    @9
    @3
    @43
    @9
    @43
    @8
    cn
    wcel
    #
    @9
    cz
    wcel
    #
    @42
    @47
    wph
    @41
    @4
    vx
    @8
    cn
    elrabi
    #
    ad2antll
    #
    @8
    mucl
    #
    syl
    #
    zred
    @41
    @3
    cn
    wcel
    #
    wph
    @42
    @3
    @0
    elfznn
    #
    ad2antrl
    #
    nndivred
    recnd
    @43
    @12
    @43
    @11
    @43
    @3
    @8
    @43
    @3
    @55
    nnrpd
    @43
    @8
    @50
    nnrpd
    rpdivcld
    relogcld
    recnd
    #
    mulcld
    #
    mulcld
    dvdsflsumcom
    wph
    @1
    @30
    @15
    vn
    @44
    @30
    @7
    @5
    @13
    vd
    csu
    #
    cmul
    co
    @15
    @44
    @29
    @58
    @7
    cmul
    @44
    @29
    @5
    @9
    @12
    cmul
    co
    #
    vd
    csu
    #
    @3
    cdiv
    co
    @5
    @59
    @3
    cdiv
    co
    #
    vd
    csu
    @58
    @44
    @28
    @60
    @3
    cdiv
    @44
    @28
    @5
    @9
    @11
    vm
    cn
    @35
    cmpt
    #
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    @60
    wph
    @41
    @28
    @3
    vn
    cn
    @65
    cmpt
    #
    cfv
    #
    @65
    wph
    @3
    cvma
    @66
    wph
    vx
    vd
    vi
    vn
    vm
    cvma
    @62
    wph
    cn
    cr
    cvma
    wf
    #
    cr
    cc
    wss
    cn
    cc
    cvma
    wf
    @68
    wph
    vmaf
    a1i
    ax-resscn
    cn
    cr
    cc
    cvma
    fss
    sylancl
    wph
    vm
    cn
    @35
    @2
    @18
    cdvds
    wbr
    vx
    cn
    crab
    vi
    cv
    cvma
    cfv
    vi
    csu
    #
    wph
    @18
    cn
    wcel
    #
    wa
    @69
    @35
    @70
    @69
    @35
    wceq
    wph
    vx
    @18
    vi
    vmasum
    adantl
    eqcomd
    mpteq2dva
    muinv
    fveq1d
    @41
    @53
    @65
    cvv
    wcel
    @67
    @65
    wceq
    @54
    @5
    @64
    vd
    sumex
    vn
    cn
    @65
    cvv
    @66
    @66
    eqid
    fvmpt2
    sylancl
    sylan9eq
    @44
    @5
    @64
    @59
    vd
    @44
    @42
    wa
    #
    @63
    @12
    @9
    cmul
    @71
    @11
    cn
    wcel
    #
    @63
    @12
    wceq
    @71
    @8
    @3
    cdvds
    wbr
    #
    @72
    @42
    @73
    @44
    @42
    @47
    @73
    @4
    @73
    vx
    @8
    cn
    @2
    @8
    @3
    cdvds
    breq1
    elrab
    simprbi
    adantl
    @44
    @53
    @47
    @73
    @72
    wb
    @42
    @41
    @53
    wph
    @54
    adantl
    #
    @49
    @3
    @8
    nndivdvds
    syl2an
    mpbid
    vm
    @11
    @35
    @12
    cn
    @62
    @18
    @11
    clog
    fveq2
    @62
    eqid
    @11
    clog
    fvex
    fvmpt
    syl
    oveq2d
    sumeq2dv
    eqtrd
    oveq1d
    @44
    @5
    @59
    @3
    vd
    @44
    c1
    @3
    cfz
    co
    #
    cfn
    wcel
    @5
    @75
    wss
    #
    @5
    cfn
    wcel
    @44
    c1
    @3
    fzfid
    @44
    @53
    @76
    @74
    @3
    vx
    dvdsssfz1
    syl
    @75
    @5
    ssfi
    syl2anc
    #
    @44
    @3
    @74
    nncnd
    #
    @71
    @9
    @12
    wph
    @41
    @42
    @9
    cc
    wcel
    #
    @43
    @9
    @52
    zcnd
    anassrs
    wph
    @41
    @42
    @12
    cc
    wcel
    @56
    anassrs
    #
    mulcld
    @44
    @3
    @74
    nnne0d
    #
    fsumdivc
    @44
    @5
    @61
    @13
    vd
    @71
    @9
    @12
    @3
    @71
    @9
    @71
    @47
    @48
    @42
    @47
    @44
    @49
    adantl
    @51
    syl
    zcnd
    @80
    @44
    @3
    cc
    wcel
    @42
    @78
    adantr
    @44
    @3
    cc0
    wne
    @42
    @81
    adantr
    div23d
    sumeq2dv
    3eqtrd
    oveq2d
    @44
    @5
    @13
    @7
    vd
    @77
    @46
    wph
    @41
    @42
    @13
    cc
    wcel
    @57
    anassrs
    fsummulc2
    eqtrd
    sumeq2dv
    wph
    @1
    @38
    @27
    vd
    wph
    @8
    @1
    wcel
    #
    wa
    #
    @38
    @17
    @33
    @37
    cmul
    co
    #
    vm
    csu
    @27
    @83
    @17
    @37
    @33
    vm
    @83
    c1
    @16
    fzfid
    @83
    @31
    @32
    @83
    @8
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
    @45
    @82
    dchrisum.b
    adantr
    @82
    @8
    cz
    wcel
    #
    wph
    @8
    c1
    @0
    elfzelz
    #
    adantl
    dchrzrhcl
    #
    @83
    @32
    @83
    @9
    @8
    @83
    @9
    @83
    @47
    @48
    wph
    @82
    @47
    @8
    cA
    cle
    wbr
    #
    wph
    cA
    cr
    wcel
    @82
    @47
    @88
    wa
    wb
    @40
    @8
    cA
    fznnfl
    syl
    simprbda
    #
    @51
    syl
    zred
    #
    @89
    nndivred
    recnd
    #
    mulcld
    @83
    @18
    @17
    wcel
    #
    wa
    #
    @34
    @36
    @93
    @18
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
    @45
    @82
    @92
    dchrisum.b
    ad2antrr
    #
    @92
    @18
    cz
    wcel
    @83
    @18
    c1
    @16
    elfzelz
    adantl
    #
    dchrzrhcl
    #
    @93
    @36
    @93
    @35
    @18
    @93
    @18
    @93
    @18
    @92
    @70
    @83
    @18
    @16
    elfznn
    adantl
    #
    nnrpd
    #
    relogcld
    #
    @97
    nndivred
    recnd
    #
    mulcld
    fsummulc2
    @83
    @17
    @84
    @26
    vm
    @93
    @84
    @31
    @34
    cmul
    co
    #
    @32
    @36
    cmul
    co
    #
    cmul
    co
    @26
    @93
    @31
    @32
    @34
    @36
    @83
    @31
    cc
    wcel
    @92
    @87
    adantr
    @83
    @32
    cc
    wcel
    @92
    @91
    adantr
    @96
    @100
    mul4d
    @93
    @21
    @101
    @25
    @102
    cmul
    @93
    @8
    @18
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
    @94
    @82
    @85
    wph
    @92
    @86
    ad2antlr
    @95
    dchrzrhmul
    @93
    @9
    @35
    cmul
    co
    @19
    cdiv
    co
    #
    @22
    @35
    cmul
    co
    #
    @102
    @25
    @93
    @79
    @35
    cc
    wcel
    #
    @19
    cc
    wcel
    @19
    cc0
    wne
    wa
    @103
    @104
    wceq
    @93
    @9
    @83
    @9
    cr
    wcel
    @92
    @90
    adantr
    recnd
    #
    @93
    @35
    @99
    recnd
    #
    @93
    @19
    @93
    @8
    @18
    @83
    @8
    crp
    wcel
    @92
    @83
    @8
    @89
    nnrpd
    adantr
    #
    @98
    rpmulcld
    rpcnne0d
    @9
    @35
    @19
    div23
    syl3anc
    @93
    @79
    @105
    @8
    cc
    wcel
    @8
    cc0
    wne
    wa
    @18
    cc
    wcel
    @18
    cc0
    wne
    wa
    @102
    @103
    wceq
    @106
    @107
    @93
    @8
    @108
    rpcnne0d
    @93
    @18
    @98
    rpcnne0d
    @9
    @35
    @8
    @18
    divmuldiv
    syl22anc
    @93
    @24
    @35
    @22
    cmul
    @93
    @23
    @18
    clog
    @93
    @18
    @8
    @93
    @18
    @97
    nncnd
    @93
    @8
    @108
    rpcnd
    @93
    @8
    @108
    rpne0d
    divcan3d
    fveq2d
    oveq2d
    3eqtr4rd
    oveq12d
    eqtr4d
    sumeq2dv
    eqtrd
    sumeq2dv
    3eqtr4d
end
