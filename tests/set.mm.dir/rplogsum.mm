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
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cprime.mm"
include "rpvmasum.mm"
include "wa.mm"
include "cn.mm"
include "phicld.mm"
include "adantr.mm"
include "nncnd.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cr.mm"
include "simpr.mm"
include "sseldi.mm"
include "elfznn.mm"
include "syl.mm"
include "vmacl.mm"
include "nndivre.mm"
include "mpancom.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "mulcld.mm"
include "relogcl.mm"
include "adantl.mm"
include "subcld.mm"
include "nnrp.mm"
include "relogcld.mm"
include "rerpdivcld.mm"
include "cc0.mm"
include "cif.mm"
include "subdid.mm"
include "wceq.mm"
include "cc.mm"
include "wne.mm"
include "0re.mm"
include "ifcl.mm"
include "rpcnne0d.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "sumeq2dv.mm"
include "fsumsub.mm"
include "inss2.mm"
include "sslin.mm"
include "mp1i.mm"
include "cdif.mm"
include "wn.mm"
include "eldif.mm"
include "incom.mm"
include "ineq2i.mm"
include "inass.mm"
include "eqtr4i.mm"
include "elin2.mm"
include "simplbi2.mm"
include "con3dimp.mm"
include "sylbi.mm"
include "iffalsed.mm"
include "oveq1d.mm"
include "eldifi.mm"
include "sylan2.mm"
include "div0.mm"
include "eqtrd.mm"
include "fsumss.mm"
include "sstri.mm"
include "iftrued.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "nnncan2d.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "resubcld.mm"
include "rpssre.mm"
include "o1const.mm"
include "sylancr.mm"
include "c2.mm"
include "a1i.mm"
include "1red.mm"
include "2re.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "breq1.mm"
include "vmaprm.mm"
include "eqcomd.mm"
include "eqle.mm"
include "syl2anc.mm"
include "vmage0.mm"
include "ifbothda.mm"
include "subge0d.mm"
include "mpbird.mm"
include "divge0d.mm"
include "fsumge0.mm"
include "absidd.mm"
include "fsumless.mm"
include "cz.mm"
include "sselda.mm"
include "flcld.mm"
include "rplogsumlem2.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "adantrr.mm"
include "elo1d.mm"
include "o1mul2.mm"
include "eqeltrrd.mm"
include "o1dif.mm"
include "mpbid.mm"

theorem rplogsum
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
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

  disjoint p x
  disjoint A p
  disjoint A x
  disjoint N p
  disjoint N x
  disjoint p ph
  disjoint ph x
  disjoint T p
  disjoint T x
  disjoint U p
  disjoint U x
  disjoint Z p
  disjoint Z x
  disjoint L p
  disjoint L x
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
  disjoint N n
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
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph u
  disjoint ph z
  disjoint d ps
  disjoint m ps
  disjoint T d
  disjoint T m
  disjoint T n
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
  disjoint U n
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
  disjoint Z n
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
  disjoint L n
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
  disjoint A n
  assert |- ( ph -> ( x e. RR+ |-> ( ( ( phi ` N ) x. sum_ p e. ( ( 1 ... ( |_ ` x ) ) i^i ( Prime i^i T ) ) ( ( log ` p ) / p ) ) - ( log ` x ) ) ) e. O(1) )

  proof
    wph
    vx
    crp
    cN
    cphi
    cfv
    #
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
    cT
    cin
    #
    vp
    cv
    #
    cvma
    cfv
    #
    @5
    cdiv
    co
    #
    vp
    csu
    #
    cmul
    co
    #
    @1
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    co1
    wcel
    vx
    crp
    @0
    @3
    cprime
    cT
    cin
    #
    cin
    #
    @5
    clog
    cfv
    #
    @5
    cdiv
    co
    #
    vp
    csu
    #
    cmul
    co
    #
    @10
    cmin
    co
    #
    cmpt
    co1
    wcel
    wph
    vx
    cA
    cT
    cU
    vp
    cL
    cN
    cZ
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.u
    rpvmasum.b
    rpvmasum.t
    rpvmasum
    wph
    vx
    crp
    @11
    @18
    wph
    @1
    crp
    wcel
    #
    wa
    #
    @9
    @10
    @20
    @0
    @8
    @20
    @0
    wph
    @0
    cn
    wcel
    @19
    wph
    cN
    rpvmasum.a
    phicld
    #
    adantr
    nncnd
    #
    @20
    @8
    @20
    @4
    @7
    vp
    @20
    @3
    cfn
    wcel
    #
    @4
    @3
    wss
    #
    @4
    cfn
    wcel
    @20
    c1
    @2
    fzfid
    #
    @3
    cT
    inss1
    #
    @3
    @4
    ssfi
    sylancl
    #
    @20
    @5
    @4
    wcel
    #
    wa
    #
    @5
    cn
    wcel
    #
    @7
    cr
    wcel
    #
    @29
    @5
    @3
    wcel
    #
    @30
    @29
    @4
    @3
    @5
    @26
    @20
    @28
    simpr
    sseldi
    @5
    @2
    elfznn
    #
    syl
    #
    @6
    cr
    wcel
    @30
    @31
    @5
    vmacl
    #
    @6
    @5
    nndivre
    mpancom
    #
    syl
    fsumrecl
    recnd
    #
    mulcld
    #
    @20
    @10
    @19
    @10
    cr
    wcel
    wph
    @1
    relogcl
    adantl
    recnd
    #
    subcld
    @20
    @17
    @10
    @20
    @0
    @16
    @22
    @20
    @16
    @20
    @13
    @15
    vp
    @20
    @23
    @13
    @3
    wss
    @13
    cfn
    wcel
    @25
    @3
    @12
    inss1
    #
    @3
    @13
    ssfi
    sylancl
    @20
    @5
    @13
    wcel
    #
    wa
    #
    @30
    @15
    cr
    wcel
    @42
    @32
    @30
    @42
    @13
    @3
    @5
    @40
    @20
    @41
    simpr
    #
    sseldi
    @33
    syl
    #
    @30
    @14
    @5
    @30
    @5
    @5
    nnrp
    #
    relogcld
    #
    @45
    rerpdivcld
    syl
    fsumrecl
    recnd
    #
    mulcld
    #
    @39
    subcld
    wph
    vx
    crp
    @0
    @4
    @6
    @5
    cprime
    wcel
    #
    @14
    cc0
    cif
    #
    cmin
    co
    #
    @5
    cdiv
    co
    #
    vp
    csu
    #
    cmul
    co
    #
    cmpt
    vx
    crp
    @11
    @18
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    crp
    @54
    @55
    @20
    @0
    @8
    @16
    cmin
    co
    #
    cmul
    co
    @9
    @17
    cmin
    co
    @54
    @55
    @20
    @0
    @8
    @16
    @22
    @37
    @47
    subdid
    @20
    @53
    @56
    @0
    cmul
    @20
    @53
    @4
    @7
    @50
    @5
    cdiv
    co
    #
    cmin
    co
    #
    vp
    csu
    @8
    @4
    @57
    vp
    csu
    #
    cmin
    co
    @56
    @20
    @4
    @52
    @58
    vp
    @29
    @30
    @52
    @58
    wceq
    #
    @34
    @30
    @6
    cc
    wcel
    @50
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
    @60
    @30
    @6
    @35
    recnd
    @30
    @50
    @30
    @14
    cr
    wcel
    #
    cc0
    cr
    wcel
    @50
    cr
    wcel
    @46
    0re
    @49
    @14
    cc0
    cr
    ifcl
    sylancl
    #
    recnd
    @30
    @5
    @45
    rpcnne0d
    #
    @6
    @50
    @5
    divsubdir
    syl3anc
    syl
    sumeq2dv
    @20
    @4
    @7
    @57
    vp
    @27
    @29
    @30
    @7
    cc
    wcel
    @34
    @30
    @7
    @36
    recnd
    syl
    @29
    @30
    @57
    cc
    wcel
    #
    @34
    @30
    @57
    @30
    @50
    @5
    @63
    @45
    rerpdivcld
    recnd
    #
    syl
    fsumsub
    @20
    @59
    @16
    @8
    cmin
    @20
    @13
    @57
    vp
    csu
    @59
    @16
    @20
    @13
    @4
    @57
    vp
    @12
    cT
    wss
    @13
    @4
    wss
    @20
    cprime
    cT
    inss2
    @12
    cT
    @3
    sslin
    mp1i
    @42
    @30
    @65
    @44
    @66
    syl
    @20
    @5
    @4
    @13
    cdif
    wcel
    #
    wa
    #
    @57
    cc0
    @5
    cdiv
    co
    #
    cc0
    @68
    @50
    cc0
    @5
    cdiv
    @68
    @49
    @14
    cc0
    @67
    @49
    wn
    #
    @20
    @67
    @28
    @41
    wn
    wa
    @70
    @5
    @4
    @13
    eldif
    @28
    @49
    @41
    @41
    @28
    @49
    @5
    @4
    cprime
    @13
    @13
    @3
    cT
    cprime
    cin
    #
    cin
    @4
    cprime
    cin
    @12
    @71
    @3
    cprime
    cT
    incom
    ineq2i
    @3
    cT
    cprime
    inass
    eqtr4i
    elin2
    simplbi2
    con3dimp
    sylbi
    adantl
    iffalsed
    oveq1d
    @68
    @30
    @69
    cc0
    wceq
    #
    @67
    @20
    @28
    @30
    @5
    @4
    @13
    eldifi
    @34
    sylan2
    @30
    @61
    @72
    @64
    @5
    div0
    syl
    syl
    eqtrd
    @27
    fsumss
    @20
    @13
    @57
    @15
    vp
    @42
    @50
    @14
    @5
    cdiv
    @42
    @49
    @14
    cc0
    @42
    @13
    cprime
    @5
    @13
    @12
    cprime
    @3
    @12
    inss2
    cprime
    cT
    inss1
    sstri
    @43
    sseldi
    iftrued
    oveq1d
    sumeq2dv
    eqtr3d
    oveq2d
    3eqtrd
    oveq2d
    @20
    @9
    @17
    @10
    @38
    @48
    @39
    nnncan2d
    3eqtr4d
    mpteq2dva
    wph
    vx
    crp
    @0
    @53
    cc
    @22
    @20
    @53
    @20
    @4
    @52
    vp
    @27
    @29
    @30
    @52
    cr
    wcel
    #
    @34
    @30
    @51
    @5
    @30
    @6
    @50
    @35
    @63
    resubcld
    #
    @45
    rerpdivcld
    #
    syl
    #
    fsumrecl
    #
    recnd
    #
    wph
    crp
    cr
    wss
    #
    @0
    cc
    wcel
    vx
    crp
    @0
    cmpt
    co1
    wcel
    rpssre
    wph
    @0
    @21
    nncnd
    vx
    crp
    @0
    o1const
    sylancr
    wph
    vx
    crp
    @53
    c1
    c2
    @79
    wph
    rpssre
    a1i
    #
    @78
    wph
    1red
    c2
    cr
    wcel
    #
    wph
    2re
    a1i
    wph
    @19
    @53
    cabs
    cfv
    #
    c2
    cle
    wbr
    c1
    @1
    cle
    wbr
    @20
    @82
    @53
    c2
    cle
    @20
    @53
    @77
    @20
    @4
    @52
    vp
    @27
    @76
    @29
    @30
    cc0
    @52
    cle
    wbr
    #
    @34
    @30
    @51
    @5
    @74
    @45
    @30
    cc0
    @51
    cle
    wbr
    @50
    @6
    cle
    wbr
    #
    @49
    @14
    @6
    cle
    wbr
    #
    cc0
    @6
    cle
    wbr
    #
    @84
    @30
    @14
    cc0
    @14
    @50
    @6
    cle
    breq1
    cc0
    @50
    @6
    cle
    breq1
    @30
    @49
    wa
    #
    @62
    @14
    @6
    wceq
    @85
    @30
    @62
    @49
    @46
    adantr
    @87
    @6
    @14
    @49
    @6
    @14
    wceq
    @30
    @5
    vmaprm
    adantl
    eqcomd
    @14
    @6
    eqle
    syl2anc
    @30
    @86
    @70
    @5
    vmage0
    adantr
    ifbothda
    @30
    @6
    @50
    @35
    @63
    subge0d
    mpbird
    divge0d
    #
    syl
    fsumge0
    absidd
    @20
    @53
    @3
    @52
    vp
    csu
    #
    c2
    @77
    @20
    @3
    @52
    vp
    @25
    @20
    @32
    wa
    #
    @30
    @73
    @32
    @30
    @20
    @33
    adantl
    #
    @75
    syl
    #
    fsumrecl
    @81
    @20
    2re
    a1i
    @20
    @3
    @52
    @4
    vp
    @25
    @92
    @90
    @30
    @83
    @91
    @88
    syl
    @24
    @20
    @26
    a1i
    fsumless
    @20
    @2
    cz
    wcel
    @89
    c2
    cle
    wbr
    @20
    @1
    wph
    crp
    cr
    @1
    @80
    sselda
    flcld
    @2
    vp
    rplogsumlem2
    syl
    letrd
    eqbrtrd
    adantrr
    elo1d
    o1mul2
    eqeltrrd
    o1dif
    mpbid
end
