include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "csu.mm"
include "cmul.mm"
include "c3.mm"
include "caddc.mm"
include "cmin.mm"
include "cabs.mm"
include "cr.mm"
include "1red.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "adantr.mm"
include "fzfid.mm"
include "simpr.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "relogcl.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "fsumrecl.mm"
include "remulcld.mm"
include "cn.mm"
include "3nn.mm"
include "nnrp.mm"
include "mp2b.mm"
include "1re.mm"
include "readdcli.mm"
include "remulcl.mm"
include "sylancl.mm"
include "wss.mm"
include "cc.mm"
include "cmpt.mm"
include "co1.mm"
include "rpssre.mm"
include "recnd.mm"
include "o1const.mm"
include "sylancr.mm"
include "crli.mm"
include "logfacrlim2.mm"
include "rlimo1.mm"
include "mp1i.mm"
include "o1mul2.mm"
include "o1add2.mm"
include "readdcld.mm"
include "wral.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "subcld.mm"
include "abscld.mm"
include "adantl.mm"
include "nndivred.mm"
include "absge0d.mm"
include "divge0d.mm"
include "fsumge0.mm"
include "absidd.mm"
include "eqeltrd.mm"
include "3re.mm"
include "a1i.mm"
include "1le3.mm"
include "jctir.mm"
include "cxr.mm"
include "clt.mm"
include "rexri.mm"
include "1lt3.mm"
include "lbico1.mm"
include "mp3an.mm"
include "0red.mm"
include "w3a.mm"
include "wb.mm"
include "elico2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "0lt1.mm"
include "simp2bi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "sylan2.mm"
include "r19.21bi.mm"
include "letrd.mm"
include "biidd.mm"
include "mpsyl.mm"
include "jca.mm"
include "log1.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "rpre.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "eqbrtrd.mm"
include "ad2antlr.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "1rp.mm"
include "logled.mm"
include "syl5eqbrr.mm"
include "rpregt0.mm"
include "divge0.mm"
include "syl21anc.mm"
include "mulge0.mm"
include "syl12anc.mm"
include "absidm.mm"
include "nndivre.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "ad3antrrr.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "rpcnne0.mm"
include "rpcnne0d.mm"
include "divdiv2.mm"
include "syl3anc.mm"
include "div23.mm"
include "eqtrd.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "syl3anbrc.mm"
include "breq1d.mm"
include "fsumharmonic.mm"
include "fsummulc2.mm"
include "breqtrrd.mm"
include "leabsd.mm"
include "adantrr.mm"
include "o1le.mm"

theorem dchrvmasumlem2
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cR: class R
  let cT: class T
  let c.1: class .1.
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
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
  let ve: setvar e
  let vr: setvar r
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cA: class A
  let cE: class E
  let cP: class P
  let wps: wff ps
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
  assume dchrvmasum.f: |- ( ( ph /\ m e. RR+ ) -> F e. CC )
  assume dchrvmasum.g: |- ( m = ( x / d ) -> F = K )
  assume dchrvmasum.c: |- ( ph -> C e. ( 0 [,) +oo ) )
  assume dchrvmasum.t: |- ( ph -> T e. CC )
  assume dchrvmasum.1: |- ( ( ph /\ m e. ( 3 [,) +oo ) ) -> ( abs ` ( F - T ) ) <_ ( C x. ( ( log ` m ) / m ) ) )
  assume dchrvmasum.r: |- ( ph -> R e. RR )
  assume dchrvmasum.2: |- ( ph -> A. m e. ( 1 [,) 3 ) ( abs ` ( F - T ) ) <_ R )

  disjoint m x
  disjoint .1. m
  disjoint .1. x
  disjoint d m
  disjoint d x
  disjoint C d
  disjoint C m
  disjoint C x
  disjoint F d
  disjoint F x
  disjoint K m
  disjoint N m
  disjoint N x
  disjoint d ph
  disjoint m ph
  disjoint ph x
  disjoint T d
  disjoint T m
  disjoint T x
  disjoint R d
  disjoint R m
  disjoint R x
  disjoint Z m
  disjoint Z x
  disjoint D m
  disjoint D x
  disjoint L d
  disjoint L m
  disjoint L x
  disjoint X d
  disjoint X m
  disjoint X x
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
  disjoint .1. y
  disjoint .1. z
  disjoint d n
  disjoint d y
  disjoint C n
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
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint E d
  disjoint E m
  disjoint E x
  disjoint E y
  disjoint K k
  disjoint m r
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
  disjoint ph z
  disjoint d ps
  disjoint m ps
  disjoint T n
  disjoint T p
  disjoint T r
  disjoint T y
  disjoint R c
  disjoint R i
  disjoint R k
  disjoint R n
  disjoint R u
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
  disjoint Z y
  disjoint Z z
  disjoint D c
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D t
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
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( x e. RR+ |-> sum_ d e. ( 1 ... ( |_ ` x ) ) ( ( abs ` ( K - T ) ) / d ) ) e. O(1) )

  proof
    wph
    vx
    crp
    cC
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
    @0
    vd
    cv
    #
    cdiv
    co
    #
    clog
    cfv
    #
    @0
    cdiv
    co
    #
    vd
    csu
    #
    cmul
    co
    #
    cR
    c3
    clog
    cfv
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @2
    cK
    cT
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    cdiv
    co
    #
    vd
    csu
    #
    c1
    cr
    wph
    1red
    wph
    vx
    crp
    @8
    @11
    cr
    wph
    @0
    crp
    wcel
    #
    wa
    #
    cC
    @7
    wph
    cC
    cr
    wcel
    #
    @17
    wph
    @19
    cc0
    cC
    cle
    wbr
    #
    wph
    cC
    cc0
    cpnf
    cico
    co
    wcel
    @19
    @20
    wa
    #
    dchrvmasum.c
    cC
    elrege0
    sylib
    #
    simpld
    #
    adantr
    #
    @18
    @2
    @6
    vd
    @18
    c1
    @1
    fzfid
    #
    @18
    @3
    @2
    wcel
    #
    wa
    #
    @5
    @0
    @27
    @4
    crp
    wcel
    #
    @5
    cr
    wcel
    #
    @18
    @17
    @3
    crp
    wcel
    @28
    @26
    wph
    @17
    simpr
    #
    @26
    @3
    @3
    @1
    elfznn
    #
    nnrpd
    @0
    @3
    rpdivcl
    syl2an
    #
    @4
    relogcl
    syl
    #
    @18
    @17
    @26
    @30
    adantr
    rerpdivcld
    #
    fsumrecl
    #
    remulcld
    #
    wph
    @11
    cr
    wcel
    #
    @17
    wph
    cR
    cr
    wcel
    #
    @10
    cr
    wcel
    @37
    dchrvmasum.r
    @9
    c1
    c3
    cn
    wcel
    c3
    crp
    wcel
    @9
    cr
    wcel
    3nn
    c3
    nnrp
    c3
    relogcl
    mp2b
    1re
    readdcli
    cR
    @10
    remulcl
    sylancl
    #
    adantr
    #
    wph
    vx
    crp
    cC
    @7
    cr
    @24
    @35
    wph
    crp
    cr
    wss
    #
    cC
    cc
    wcel
    #
    vx
    crp
    cC
    cmpt
    co1
    wcel
    rpssre
    wph
    cC
    @23
    recnd
    #
    vx
    crp
    cC
    o1const
    sylancr
    vx
    crp
    @7
    cmpt
    #
    c1
    crli
    wbr
    @44
    co1
    wcel
    wph
    vx
    vd
    logfacrlim2
    c1
    @44
    rlimo1
    mp1i
    o1mul2
    wph
    @41
    @11
    cc
    wcel
    vx
    crp
    @11
    cmpt
    co1
    wcel
    rpssre
    wph
    @11
    @39
    recnd
    vx
    crp
    @11
    o1const
    sylancr
    o1add2
    @18
    @8
    @11
    @36
    @40
    readdcld
    #
    @18
    @16
    @18
    @2
    @15
    vd
    @25
    @27
    @14
    @3
    @27
    @13
    @27
    cK
    cT
    @27
    @28
    cF
    cc
    wcel
    #
    vm
    crp
    wral
    #
    cK
    cc
    wcel
    #
    @32
    wph
    @47
    @17
    @26
    wph
    @46
    vm
    crp
    dchrvmasum.f
    ralrimiva
    ad2antrr
    @46
    @48
    vm
    @4
    crp
    vm
    cv
    #
    @4
    wceq
    #
    cF
    cK
    cc
    dchrvmasum.g
    eleq1d
    rspcv
    sylc
    wph
    cT
    cc
    wcel
    #
    @17
    @26
    dchrvmasum.t
    ad2antrr
    subcld
    #
    abscld
    #
    @26
    @3
    cn
    wcel
    #
    @18
    @31
    adantl
    #
    nndivred
    #
    fsumrecl
    #
    recnd
    wph
    @17
    @16
    cabs
    cfv
    #
    @12
    cabs
    cfv
    #
    cle
    wbr
    c1
    @0
    cle
    wbr
    @18
    @58
    @12
    @59
    @18
    @58
    @16
    cr
    @18
    @16
    @57
    @18
    @2
    @15
    vd
    @25
    @56
    @27
    @14
    @3
    @53
    @27
    @3
    @55
    nnrpd
    #
    @27
    @13
    @52
    absge0d
    divge0d
    fsumge0
    absidd
    @57
    eqeltrd
    @45
    @18
    @12
    @18
    @12
    @45
    recnd
    abscld
    @18
    @58
    @2
    cC
    @6
    cmul
    co
    #
    vd
    csu
    #
    @11
    caddc
    co
    @12
    cle
    @18
    @0
    @14
    @61
    cR
    c3
    vd
    @30
    @18
    c3
    cr
    wcel
    #
    c1
    c3
    cle
    wbr
    @63
    @18
    3re
    a1i
    1le3
    jctir
    @18
    @38
    cc0
    cR
    cle
    wbr
    #
    wph
    @38
    @17
    dchrvmasum.r
    adantr
    wph
    @64
    @17
    c1
    c1
    c3
    cico
    co
    #
    wcel
    #
    wph
    @64
    vm
    @65
    wral
    @64
    c1
    cxr
    wcel
    c3
    cxr
    wcel
    #
    c1
    c3
    clt
    wbr
    @66
    c1
    1re
    rexri
    c3
    3re
    rexri
    #
    1lt3
    c1
    c3
    lbico1
    mp3an
    wph
    @64
    vm
    @65
    wph
    @49
    @65
    wcel
    #
    wa
    #
    cc0
    cF
    cT
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    @70
    0red
    @69
    wph
    @49
    crp
    wcel
    #
    @72
    cr
    wcel
    @69
    @49
    @69
    @49
    cr
    wcel
    #
    c1
    @49
    cle
    wbr
    #
    @49
    c3
    clt
    wbr
    #
    c1
    cr
    wcel
    #
    @67
    @69
    @74
    @75
    @76
    w3a
    wb
    1re
    @68
    c1
    c3
    @49
    elico2
    mp2an
    #
    simp1bi
    #
    @69
    cc0
    c1
    @49
    @69
    0red
    @69
    1red
    @79
    cc0
    c1
    clt
    wbr
    @69
    0lt1
    a1i
    @69
    @74
    @75
    @76
    @78
    simp2bi
    ltletrd
    elrpd
    #
    wph
    @73
    wa
    #
    @71
    @81
    cF
    cT
    dchrvmasum.f
    wph
    @51
    @73
    dchrvmasum.t
    adantr
    subcld
    #
    abscld
    sylan2
    wph
    @38
    @69
    dchrvmasum.r
    adantr
    @69
    wph
    @73
    cc0
    @72
    cle
    wbr
    @80
    @81
    @71
    @82
    absge0d
    sylan2
    wph
    @72
    cR
    cle
    wbr
    #
    vm
    @65
    dchrvmasum.2
    r19.21bi
    letrd
    ralrimiva
    @64
    @64
    vm
    c1
    @65
    @49
    c1
    wceq
    @64
    biidd
    rspcv
    mpsyl
    adantr
    jca
    @27
    @14
    @53
    recnd
    @27
    cC
    @6
    wph
    @19
    @17
    @26
    @23
    ad2antrr
    @34
    remulcld
    @27
    @21
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    #
    cc0
    @61
    cle
    wbr
    wph
    @21
    @17
    @26
    @22
    ad2antrr
    @34
    @27
    @29
    cc0
    @5
    cle
    wbr
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    wa
    #
    @84
    @33
    @27
    cc0
    c1
    clog
    cfv
    #
    @5
    cle
    log1
    @27
    c1
    @4
    cle
    wbr
    #
    @87
    @5
    cle
    wbr
    @27
    c1
    @3
    cmul
    co
    #
    @0
    cle
    wbr
    @88
    @27
    @89
    @3
    @0
    cle
    @27
    @3
    @27
    @3
    @55
    nncnd
    #
    mulid2d
    @18
    @26
    @54
    @3
    @0
    cle
    wbr
    #
    @18
    @85
    @26
    @54
    @91
    wa
    wb
    @17
    @85
    wph
    @0
    rpre
    #
    adantl
    #
    @3
    @0
    fznnfl
    syl
    simplbda
    eqbrtrd
    @27
    c1
    @0
    @3
    @27
    1red
    @17
    @85
    wph
    @26
    @92
    ad2antlr
    @60
    lemuldivd
    mpbid
    #
    @27
    c1
    @4
    c1
    crp
    wcel
    @27
    1rp
    a1i
    @32
    logled
    mpbid
    syl5eqbrr
    @17
    @86
    wph
    @26
    @0
    rpregt0
    ad2antlr
    @5
    @0
    divge0
    syl21anc
    cC
    @6
    mulge0
    syl12anc
    @27
    c3
    @4
    cle
    wbr
    #
    wa
    #
    @14
    cabs
    cfv
    #
    @14
    @61
    @3
    cmul
    co
    #
    cle
    @27
    @97
    @14
    wceq
    #
    @95
    @27
    @13
    cc
    wcel
    @99
    @52
    @13
    absidm
    syl
    #
    adantr
    @96
    @14
    cC
    @5
    @4
    cdiv
    co
    #
    cmul
    co
    #
    @98
    cle
    @96
    @4
    c3
    cpnf
    cico
    co
    #
    wcel
    #
    @72
    cC
    @49
    clog
    cfv
    #
    @49
    cdiv
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vm
    @103
    wral
    #
    @14
    @102
    cle
    wbr
    #
    @96
    @4
    cr
    wcel
    #
    @95
    @104
    @27
    @111
    @95
    @18
    @85
    @54
    @111
    @26
    @93
    @31
    @0
    @3
    nndivre
    syl2an
    #
    adantr
    @27
    @95
    simpr
    @63
    @104
    @111
    @95
    wa
    wb
    3re
    c3
    @4
    elicopnf
    ax-mp
    sylanbrc
    wph
    @109
    @17
    @26
    @95
    wph
    @108
    vm
    @103
    dchrvmasum.1
    ralrimiva
    ad3antrrr
    @108
    @110
    vm
    @4
    @103
    @50
    @72
    @14
    @107
    @102
    cle
    @50
    @71
    @13
    cabs
    @50
    cF
    cK
    cT
    cmin
    dchrvmasum.g
    oveq1d
    fveq2d
    #
    @50
    @106
    @101
    cC
    cmul
    @50
    @105
    @5
    @49
    @4
    cdiv
    @49
    @4
    clog
    fveq2
    @50
    id
    oveq12d
    oveq2d
    breq12d
    rspcv
    sylc
    @27
    @102
    @98
    wceq
    @95
    @27
    @102
    cC
    @6
    @3
    cmul
    co
    #
    cmul
    co
    @98
    @27
    @101
    @114
    cC
    cmul
    @27
    @101
    @5
    @3
    cmul
    co
    @0
    cdiv
    co
    #
    @114
    @27
    @5
    cc
    wcel
    #
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    #
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    wa
    @101
    @115
    wceq
    @27
    @5
    @33
    recnd
    #
    @17
    @117
    wph
    @26
    @0
    rpcnne0
    ad2antlr
    #
    @27
    @3
    @60
    rpcnne0d
    @5
    @0
    @3
    divdiv2
    syl3anc
    @27
    @116
    @118
    @117
    @115
    @114
    wceq
    @119
    @90
    @120
    @5
    @3
    @0
    div23
    syl3anc
    eqtrd
    oveq2d
    @27
    cC
    @6
    @3
    wph
    @42
    @17
    @26
    @43
    ad2antrr
    @27
    @6
    @34
    recnd
    #
    @90
    mulassd
    eqtr4d
    adantr
    breqtrd
    eqbrtrd
    @27
    @4
    c3
    clt
    wbr
    #
    wa
    #
    @97
    @14
    cR
    cle
    @27
    @99
    @122
    @100
    adantr
    @123
    @4
    @65
    wcel
    #
    @83
    vm
    @65
    wral
    #
    @14
    cR
    cle
    wbr
    #
    @123
    @111
    @88
    @122
    @124
    @27
    @111
    @122
    @112
    adantr
    @27
    @88
    @122
    @94
    adantr
    @27
    @122
    simpr
    @77
    @67
    @124
    @111
    @88
    @122
    w3a
    wb
    1re
    @68
    c1
    c3
    @4
    elico2
    mp2an
    syl3anbrc
    wph
    @125
    @17
    @26
    @122
    dchrvmasum.2
    ad3antrrr
    @83
    @126
    vm
    @4
    @65
    @50
    @72
    @14
    cR
    cle
    @113
    breq1d
    rspcv
    sylc
    eqbrtrd
    fsumharmonic
    @18
    @8
    @62
    @11
    caddc
    @18
    @2
    @6
    cC
    vd
    @25
    wph
    @42
    @17
    @43
    adantr
    @121
    fsummulc2
    oveq1d
    breqtrrd
    @18
    @12
    @45
    leabsd
    letrd
    adantrr
    o1le
end
