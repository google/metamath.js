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
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rpred.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "elrabi.mm"
include "ad2antll.mm"
include "mucl.mm"
include "syl.mm"
include "zcnd.mm"
include "cc.mm"
include "adantr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "dchrzrhcl.mm"
include "elfznn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "crp.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "adantrr.mm"
include "dvdsflsumcom.mm"
include "fzfid.mm"
include "wss.mm"
include "ssriv.mm"
include "a1i.mm"
include "cuz.mm"
include "cr.mm"
include "cle.mm"
include "flge1nn.mm"
include "syl2anc.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "musumsum.mm"
include "dchrzrh1.mm"
include "oveq1d.mm"
include "1div1e1.mm"
include "syl6eq.mm"
include "rpcnd.mm"
include "div1d.mm"
include "mulid2d.mm"
include "3eqtrrd.mm"
include "wb.mm"
include "fznnfl.mm"
include "simprbda.mm"
include "zred.mm"
include "nndivred.mm"
include "ad2antrr.mm"
include "fsummulc2.mm"
include "cc0.mm"
include "wne.mm"
include "rpcnne0d.mm"
include "div12.mm"
include "syl3anc.mm"
include "rpne0d.mm"
include "mulassd.mm"
include "mul4d.mm"
include "ad2antlr.mm"
include "dchrzrhmul.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "eqtr4d.mm"
include "divdiv1.mm"
include "eqcomd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "sumeq2dv.mm"

theorem dchrvmasum2lem
  let wph: wff ph
  let cA: class A
  let cD: class D
  let c.1: class .1.
  let vm: setvar m
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vn: setvar n
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
  assume dchrvmasum2.2: |- ( ph -> 1 <_ A )

  disjoint .1. m
  disjoint d m
  disjoint A d
  disjoint A m
  disjoint N m
  disjoint d ph
  disjoint m ph
  disjoint Z m
  disjoint D m
  disjoint L d
  disjoint L m
  disjoint X d
  disjoint X m
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
  disjoint .1. y
  disjoint .1. z
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
  disjoint N n
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
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( log ` A ) = sum_ d e. ( 1 ... ( |_ ` A ) ) ( ( ( X ` ( L ` d ) ) x. ( ( mmu ` d ) / d ) ) x. sum_ m e. ( 1 ... ( |_ ` ( A / d ) ) ) ( ( X ` ( L ` m ) ) x. ( ( log ` ( ( A / d ) / m ) ) / m ) ) ) )

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
    vd
    cv
    #
    cmu
    cfv
    #
    @2
    cL
    cfv
    #
    cX
    cfv
    #
    @2
    cdiv
    co
    #
    cA
    @2
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
    vn
    csu
    #
    @1
    c1
    cA
    @5
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @6
    @5
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
    @19
    cdiv
    co
    #
    cA
    @19
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
    cA
    clog
    cfv
    #
    @1
    @5
    cL
    cfv
    cX
    cfv
    #
    @6
    @5
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
    @15
    @18
    cdiv
    co
    #
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
    @13
    @26
    vm
    vn
    vd
    @2
    @19
    wceq
    #
    @12
    @25
    @6
    cmul
    @38
    @9
    @22
    @11
    @24
    cmul
    @38
    @8
    @21
    @2
    @19
    cdiv
    @38
    @7
    @20
    cX
    @2
    @19
    cL
    fveq2
    fveq2d
    @38
    id
    oveq12d
    @38
    @10
    @23
    clog
    @2
    @19
    cA
    cdiv
    oveq2
    fveq2d
    oveq12d
    oveq2d
    wph
    cA
    dchrvmasum.a
    rpred
    #
    wph
    @2
    @1
    wcel
    #
    @5
    @4
    wcel
    #
    wa
    wa
    #
    @6
    @12
    @42
    @6
    @42
    @5
    cn
    wcel
    #
    @6
    cz
    wcel
    #
    @41
    @43
    wph
    @40
    @3
    vx
    @5
    cn
    elrabi
    ad2antll
    @5
    mucl
    #
    syl
    zcnd
    wph
    @40
    @12
    cc
    wcel
    @41
    wph
    @40
    wa
    #
    @9
    @11
    @46
    @8
    @2
    @46
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
    cX
    cD
    wcel
    #
    @40
    dchrisum.b
    adantr
    @40
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
    @46
    @2
    @40
    @2
    cn
    wcel
    wph
    @2
    @0
    elfznn
    #
    adantl
    #
    nncnd
    @46
    @2
    @49
    nnne0d
    divcld
    @46
    @11
    @46
    @10
    wph
    cA
    crp
    wcel
    #
    @2
    crp
    wcel
    @10
    crp
    wcel
    @40
    dchrvmasum.a
    @40
    @2
    @48
    nnrpd
    cA
    @2
    rpdivcl
    syl2an
    relogcld
    recnd
    mulcld
    #
    adantrr
    mulcld
    dvdsflsumcom
    wph
    @14
    c1
    cL
    cfv
    #
    cX
    cfv
    #
    c1
    cdiv
    co
    #
    cA
    c1
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    c1
    @28
    cmul
    co
    @28
    wph
    @1
    @12
    @57
    vd
    vn
    vx
    @2
    c1
    wceq
    #
    @9
    @54
    @11
    @56
    cmul
    @58
    @8
    @53
    @2
    c1
    cdiv
    @58
    @7
    @52
    cX
    @2
    c1
    cL
    fveq2
    fveq2d
    @58
    id
    oveq12d
    @58
    @10
    @55
    clog
    @2
    c1
    cA
    cdiv
    oveq2
    fveq2d
    oveq12d
    wph
    c1
    @0
    fzfid
    @1
    cn
    wss
    wph
    vn
    @1
    cn
    @48
    ssriv
    a1i
    wph
    @0
    c1
    cuz
    cfv
    #
    wcel
    c1
    @1
    wcel
    wph
    @0
    cn
    @59
    wph
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    @0
    cn
    wcel
    @39
    dchrvmasum2.2
    cA
    flge1nn
    syl2anc
    nnuz
    syl6eleq
    c1
    @0
    eluzfz1
    syl
    @51
    musumsum
    wph
    @54
    c1
    @56
    @28
    cmul
    wph
    @54
    c1
    c1
    cdiv
    co
    c1
    wph
    @53
    c1
    c1
    cdiv
    wph
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
    dchrisum.b
    dchrzrh1
    oveq1d
    1div1e1
    syl6eq
    wph
    @55
    cA
    clog
    wph
    cA
    wph
    cA
    dchrvmasum.a
    rpcnd
    #
    div1d
    fveq2d
    oveq12d
    wph
    @28
    wph
    @28
    wph
    cA
    dchrvmasum.a
    relogcld
    recnd
    mulid2d
    3eqtrrd
    wph
    @1
    @37
    @27
    vd
    wph
    @5
    @1
    wcel
    #
    wa
    #
    @37
    @17
    @31
    @36
    cmul
    co
    #
    vm
    csu
    @27
    @63
    @17
    @36
    @31
    vm
    @63
    c1
    @16
    fzfid
    @63
    @29
    @30
    @63
    @5
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
    @47
    @62
    dchrisum.b
    adantr
    @62
    @5
    cz
    wcel
    #
    wph
    @5
    c1
    @0
    elfzelz
    #
    adantl
    dchrzrhcl
    #
    @63
    @30
    @63
    @6
    @5
    @63
    @6
    @63
    @43
    @44
    wph
    @62
    @43
    @5
    cA
    cle
    wbr
    #
    wph
    @60
    @62
    @43
    @68
    wa
    wb
    @39
    @5
    cA
    fznnfl
    syl
    simprbda
    #
    @45
    syl
    zred
    #
    @69
    nndivred
    recnd
    mulcld
    @63
    @18
    @17
    wcel
    #
    wa
    #
    @32
    @35
    @72
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
    @47
    @62
    @71
    dchrisum.b
    ad2antrr
    #
    @71
    @18
    cz
    wcel
    @63
    @18
    c1
    @16
    elfzelz
    adantl
    #
    dchrzrhcl
    #
    @72
    @35
    @72
    @34
    @18
    @72
    @33
    @63
    @15
    crp
    wcel
    #
    @18
    crp
    wcel
    @33
    crp
    wcel
    @71
    wph
    @50
    @5
    crp
    wcel
    #
    @76
    @62
    dchrvmasum.a
    @62
    @5
    @5
    @0
    elfznn
    nnrpd
    cA
    @5
    rpdivcl
    syl2an
    @71
    @18
    @18
    @16
    elfznn
    #
    nnrpd
    @15
    @18
    rpdivcl
    syl2an
    relogcld
    #
    @71
    @18
    cn
    wcel
    @63
    @78
    adantl
    #
    nndivred
    recnd
    mulcld
    fsummulc2
    @63
    @17
    @64
    @26
    vm
    @72
    @64
    @6
    @29
    @5
    cdiv
    co
    #
    cmul
    co
    #
    @34
    @32
    @18
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @26
    @72
    @31
    @82
    @36
    @84
    cmul
    @72
    @29
    cc
    wcel
    #
    @6
    cc
    wcel
    @5
    cc
    wcel
    @5
    cc0
    wne
    wa
    #
    @31
    @82
    wceq
    @63
    @86
    @71
    @67
    adantr
    #
    @72
    @6
    @63
    @6
    cr
    wcel
    @71
    @70
    adantr
    recnd
    #
    @72
    @5
    @63
    @77
    @71
    @63
    @5
    @69
    nnrpd
    adantr
    #
    rpcnne0d
    #
    @29
    @6
    @5
    div12
    syl3anc
    @72
    @32
    cc
    wcel
    #
    @34
    cc
    wcel
    @18
    cc
    wcel
    @18
    cc0
    wne
    wa
    #
    @36
    @84
    wceq
    @75
    @72
    @34
    @79
    recnd
    #
    @72
    @18
    @72
    @18
    @80
    nnrpd
    rpcnne0d
    #
    @32
    @34
    @18
    div12
    syl3anc
    oveq12d
    @72
    @6
    @34
    cmul
    co
    @81
    @83
    cmul
    co
    #
    cmul
    co
    @6
    @34
    @96
    cmul
    co
    #
    cmul
    co
    @85
    @26
    @72
    @6
    @34
    @96
    @89
    @94
    @72
    @81
    @83
    @72
    @29
    @5
    @88
    @72
    @5
    @90
    rpcnd
    @72
    @5
    @90
    rpne0d
    divcld
    #
    @72
    @32
    @18
    @75
    @72
    @18
    @80
    nncnd
    @72
    @18
    @80
    nnne0d
    divcld
    #
    mulcld
    #
    mulassd
    @72
    @6
    @81
    @34
    @83
    @89
    @98
    @94
    @99
    mul4d
    @72
    @25
    @97
    @6
    cmul
    @72
    @25
    @96
    @34
    cmul
    co
    @97
    @72
    @22
    @96
    @24
    @34
    cmul
    @72
    @22
    @29
    @32
    cmul
    co
    #
    @19
    cdiv
    co
    #
    @96
    @72
    @21
    @101
    @19
    cdiv
    @72
    @5
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
    @73
    @62
    @65
    wph
    @71
    @66
    ad2antlr
    @74
    dchrzrhmul
    oveq1d
    @72
    @86
    @92
    @87
    @93
    @96
    @102
    wceq
    @88
    @75
    @91
    @95
    @29
    @32
    @5
    @18
    divmuldiv
    syl22anc
    eqtr4d
    @72
    @23
    @33
    clog
    @72
    @33
    @23
    @72
    cA
    cc
    wcel
    #
    @87
    @93
    @33
    @23
    wceq
    wph
    @103
    @62
    @71
    @61
    ad2antrr
    @91
    @95
    cA
    @5
    @18
    divdiv1
    syl3anc
    eqcomd
    fveq2d
    oveq12d
    @72
    @96
    @34
    @100
    @94
    mulcomd
    eqtrd
    oveq2d
    3eqtr4d
    eqtrd
    sumeq2dv
    eqtrd
    sumeq2dv
    3eqtr4d
end
