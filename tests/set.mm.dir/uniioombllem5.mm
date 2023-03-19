include "cin.mm"
include "covol.mm"
include "cfv.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "c4.mm"
include "cmul.mm"
include "wss.mm"
include "cr.mm"
include "wcel.mm"
include "inss1.mm"
include "a1i.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cicc.mm"
include "cc0.mm"
include "wceq.mm"
include "uniiccdif.mm"
include "simpld.mm"
include "cn.mm"
include "cle.mm"
include "cxp.mm"
include "wf.mm"
include "ovolficcss.mm"
include "syl.mm"
include "sstrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "difssd.mm"
include "readdcld.mm"
include "c1.mm"
include "cfz.mm"
include "cima.mm"
include "imassrn.mm"
include "unissi.mm"
include "eqsstri.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "uniioombllem1.mm"
include "ssid.mm"
include "ovollb.mm"
include "sylancl.mm"
include "ovollecl.mm"
include "rpred.mm"
include "4re.mm"
include "remulcl.mm"
include "sylancr.mm"
include "uniioombllem3.mm"
include "ltled.mm"
include "uniioombllem4.mm"
include "3sstr4i.mm"
include "sscon.mm"
include "mp1i.mm"
include "ovolss.mm"
include "syl2anc.mm"
include "le2addd.mm"
include "recnd.mm"
include "add32d.mm"
include "cvol.mm"
include "cdm.mm"
include "cv.mm"
include "ciun.mm"
include "cpw.mm"
include "wfun.mm"
include "ioof.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "fco.mm"
include "ffun.mm"
include "funiunfv.mm"
include "3syl.mm"
include "syl6eqr.mm"
include "cfn.mm"
include "wral.mm"
include "fzfid.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "elfznn.mm"
include "fvco3.mm"
include "syl2an.mm"
include "cop.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "eqtrd.mm"
include "ioombl.mm"
include "syl6eqel.mm"
include "ralrimiva.mm"
include "finiunmbl.mm"
include "eqeltrrd.mm"
include "mblsplit.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "leadd1dd.mm"
include "addassd.mm"
include "c2.mm"
include "2t2e4.mm"
include "oveq1i.mm"
include "2cnd.mm"
include "mulassd.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "syl5eqr.mm"

theorem uniioombllem5
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let va: setvar a
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  let cH: class H
  let cJ: class J
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume uniioombl.a: |- A = U. ran ( (,) o. F )
  assume uniioombl.e: |- ( ph -> ( vol* ` E ) e. RR )
  assume uniioombl.c: |- ( ph -> C e. RR+ )
  assume uniioombl.g: |- ( ph -> G : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.s: |- ( ph -> E C_ U. ran ( (,) o. G ) )
  assume uniioombl.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume uniioombl.v: |- ( ph -> sup ( ran T , RR* , < ) <_ ( ( vol* ` E ) + C ) )
  assume uniioombl.m: |- ( ph -> M e. NN )
  assume uniioombl.m2: |- ( ph -> ( abs ` ( ( T ` M ) - sup ( ran T , RR* , < ) ) ) < C )
  assume uniioombl.k: |- K = U. ( ( (,) o. G ) " ( 1 ... M ) )
  assume uniioombl.n: |- ( ph -> N e. NN )
  assume uniioombl.n2: |- ( ph -> A. j e. ( 1 ... M ) ( abs ` ( sum_ i e. ( 1 ... N ) ( vol* ` ( ( (,) ` ( F ` i ) ) i^i ( (,) ` ( G ` j ) ) ) ) - ( vol* ` ( ( (,) ` ( G ` j ) ) i^i A ) ) ) ) < ( C / M ) )
  assume uniioombl.l: |- L = U. ( ( (,) o. F ) " ( 1 ... N ) )

  disjoint i j
  disjoint i x
  disjoint F i
  disjoint j x
  disjoint F j
  disjoint F x
  disjoint G i
  disjoint G j
  disjoint G x
  disjoint K j
  disjoint K x
  disjoint A j
  disjoint A x
  disjoint C i
  disjoint C j
  disjoint C x
  disjoint M i
  disjoint M j
  disjoint M x
  disjoint N i
  disjoint N j
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint T i
  disjoint T j
  disjoint T x
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i y
  disjoint i z
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j y
  disjoint j z
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a w
  disjoint G a
  disjoint i m
  disjoint i w
  disjoint j m
  disjoint j w
  disjoint k m
  disjoint k w
  disjoint G k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n w
  disjoint G n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint K n
  disjoint K y
  disjoint K z
  disjoint A a
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C y
  disjoint C z
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint E m
  disjoint E n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N n
  disjoint N z
  disjoint S n
  disjoint S y
  disjoint a ph
  disjoint f m
  disjoint f ph
  disjoint k ph
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint T a
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T y
  disjoint T z
  assert |- ( ph -> ( ( vol* ` ( E i^i A ) ) + ( vol* ` ( E \ A ) ) ) <_ ( ( vol* ` E ) + ( 4 x. C ) ) )

  proof
    wph
    cE
    cA
    cin
    #
    covol
    cfv
    #
    cE
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    cK
    cA
    cin
    #
    covol
    cfv
    #
    cK
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    cC
    cC
    caddc
    co
    #
    caddc
    co
    #
    cE
    covol
    cfv
    #
    c4
    cC
    cmul
    co
    #
    caddc
    co
    #
    wph
    @1
    @3
    wph
    @0
    cE
    wss
    #
    cE
    cr
    wss
    #
    @12
    cr
    wcel
    #
    @1
    cr
    wcel
    @15
    wph
    cE
    cA
    inss1
    a1i
    wph
    cE
    cioo
    cG
    ccom
    #
    crn
    #
    cuni
    #
    cr
    uniioombl.s
    wph
    @20
    cicc
    cG
    ccom
    crn
    cuni
    #
    cr
    wph
    @20
    @21
    wss
    @21
    @20
    cdif
    covol
    cfv
    cc0
    wceq
    wph
    cG
    uniioombl.g
    uniiccdif
    simpld
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cG
    wf
    #
    @21
    cr
    wss
    uniioombl.g
    cG
    ovolficcss
    syl
    sstrd
    #
    sstrd
    #
    uniioombl.e
    @0
    cE
    ovolsscl
    syl3anc
    wph
    @2
    cE
    wss
    @16
    @17
    @3
    cr
    wcel
    wph
    cE
    cA
    difssd
    @26
    uniioombl.e
    @2
    cE
    ovolsscl
    syl3anc
    readdcld
    #
    wph
    @9
    @10
    wph
    @6
    @8
    wph
    @5
    cK
    wss
    #
    cK
    cr
    wss
    #
    cK
    covol
    cfv
    #
    cr
    wcel
    #
    @6
    cr
    wcel
    @28
    wph
    cK
    cA
    inss1
    a1i
    wph
    cK
    @20
    cr
    cK
    @20
    wss
    #
    wph
    cK
    @18
    c1
    cM
    cfz
    co
    #
    cima
    #
    cuni
    @20
    uniioombl.k
    @34
    @19
    @18
    @33
    imassrn
    unissi
    eqsstri
    #
    a1i
    #
    @25
    sstrd
    #
    wph
    @32
    @20
    cr
    wss
    #
    @20
    covol
    cfv
    #
    cr
    wcel
    #
    @31
    @36
    @25
    wph
    @38
    cT
    crn
    cxr
    clt
    csup
    #
    cr
    wcel
    @39
    @41
    cle
    wbr
    #
    @40
    @25
    wph
    vx
    cA
    cC
    cS
    cT
    cE
    cF
    cG
    uniioombl.1
    uniioombl.2
    uniioombl.3
    uniioombl.a
    uniioombl.e
    uniioombl.c
    uniioombl.g
    uniioombl.s
    uniioombl.t
    uniioombl.v
    uniioombllem1
    #
    wph
    @24
    @20
    @20
    wss
    @42
    uniioombl.g
    @20
    ssid
    @20
    cT
    cG
    uniioombl.t
    ovollb
    sylancl
    @20
    @41
    ovollecl
    syl3anc
    cK
    @20
    ovolsscl
    syl3anc
    #
    @5
    cK
    ovolsscl
    syl3anc
    #
    wph
    @7
    cK
    wss
    @29
    @31
    @8
    cr
    wcel
    wph
    cK
    cA
    difssd
    @37
    @44
    @7
    cK
    ovolsscl
    syl3anc
    #
    readdcld
    #
    wph
    cC
    cC
    wph
    cC
    uniioombl.c
    rpred
    #
    @48
    readdcld
    #
    readdcld
    #
    wph
    @12
    @13
    uniioombl.e
    wph
    c4
    cr
    wcel
    cC
    cr
    wcel
    @13
    cr
    wcel
    4re
    @48
    c4
    cC
    remulcl
    sylancr
    readdcld
    wph
    @4
    @11
    @27
    @50
    wph
    vx
    cA
    cC
    cS
    cT
    cE
    cF
    cG
    cK
    cM
    uniioombl.1
    uniioombl.2
    uniioombl.3
    uniioombl.a
    uniioombl.e
    uniioombl.c
    uniioombl.g
    uniioombl.s
    uniioombl.t
    uniioombl.v
    uniioombl.m
    uniioombl.m2
    uniioombl.k
    uniioombllem3
    ltled
    wph
    @11
    @12
    @10
    caddc
    co
    #
    @10
    caddc
    co
    #
    @14
    cle
    wph
    @9
    @51
    @10
    @47
    wph
    @12
    @10
    uniioombl.e
    @49
    readdcld
    #
    @49
    wph
    @9
    @30
    cC
    caddc
    co
    #
    @51
    @47
    wph
    @30
    cC
    @44
    @48
    readdcld
    @53
    wph
    @9
    cK
    cL
    cin
    #
    covol
    cfv
    #
    cC
    caddc
    co
    #
    cK
    cL
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @54
    cle
    wph
    @6
    @8
    @57
    @59
    @45
    @46
    wph
    @56
    cC
    wph
    @55
    cK
    wss
    #
    @29
    @31
    @56
    cr
    wcel
    @61
    wph
    cK
    cL
    inss1
    a1i
    @37
    @44
    @55
    cK
    ovolsscl
    syl3anc
    #
    @48
    readdcld
    wph
    @58
    cK
    wss
    @29
    @31
    @59
    cr
    wcel
    wph
    cK
    cL
    difssd
    #
    @37
    @44
    @58
    cK
    ovolsscl
    syl3anc
    #
    wph
    vx
    cA
    cC
    cS
    cT
    vi
    vj
    cE
    cF
    cG
    cK
    cL
    cM
    cN
    uniioombl.1
    uniioombl.2
    uniioombl.3
    uniioombl.a
    uniioombl.e
    uniioombl.c
    uniioombl.g
    uniioombl.s
    uniioombl.t
    uniioombl.v
    uniioombl.m
    uniioombl.m2
    uniioombl.k
    uniioombl.n
    uniioombl.n2
    uniioombl.l
    uniioombllem4
    wph
    @7
    @58
    wss
    #
    @58
    cr
    wss
    @8
    @59
    cle
    wbr
    cL
    cA
    wss
    @65
    wph
    cioo
    cF
    ccom
    #
    c1
    cN
    cfz
    co
    #
    cima
    #
    cuni
    #
    @66
    crn
    #
    cuni
    cL
    cA
    @68
    @70
    @66
    @67
    imassrn
    unissi
    uniioombl.l
    uniioombl.a
    3sstr4i
    cL
    cA
    cK
    sscon
    mp1i
    wph
    @58
    cK
    cr
    @63
    @37
    sstrd
    @7
    @58
    ovolss
    syl2anc
    le2addd
    wph
    @60
    @56
    @59
    caddc
    co
    #
    cC
    caddc
    co
    @54
    wph
    @56
    cC
    @59
    wph
    @56
    @62
    recnd
    wph
    cC
    @48
    recnd
    #
    wph
    @59
    @64
    recnd
    add32d
    wph
    @30
    @71
    cC
    caddc
    wph
    cL
    cvol
    cdm
    #
    wcel
    @29
    @31
    @30
    @71
    wceq
    wph
    vn
    @67
    vn
    cv
    #
    @66
    cfv
    #
    ciun
    #
    cL
    @73
    wph
    @76
    @69
    cL
    wph
    cn
    cr
    cpw
    #
    @66
    wf
    #
    @66
    wfun
    @76
    @69
    wceq
    wph
    cxr
    cxr
    cxp
    #
    @77
    cioo
    wf
    cn
    @79
    cF
    wf
    #
    @78
    ioof
    wph
    cn
    @23
    cF
    wf
    #
    @23
    @79
    wss
    @80
    uniioombl.1
    @23
    @22
    @79
    cle
    @22
    inss2
    #
    rexpssxrxp
    sstri
    cn
    @23
    @79
    cF
    fss
    sylancl
    cn
    @79
    @77
    cioo
    cF
    fco
    sylancr
    cn
    @77
    @66
    ffun
    vn
    @67
    @66
    funiunfv
    3syl
    uniioombl.l
    syl6eqr
    wph
    @67
    cfn
    wcel
    @75
    @73
    wcel
    #
    vn
    @67
    wral
    @76
    @73
    wcel
    wph
    c1
    cN
    fzfid
    wph
    @83
    vn
    @67
    wph
    @74
    @67
    wcel
    #
    wa
    #
    @75
    @74
    cF
    cfv
    #
    c1st
    cfv
    #
    @86
    c2nd
    cfv
    #
    cioo
    co
    #
    @73
    @85
    @75
    @86
    cioo
    cfv
    #
    @89
    wph
    @81
    @74
    cn
    wcel
    #
    @75
    @90
    wceq
    @84
    uniioombl.1
    @74
    cN
    elfznn
    #
    cn
    @23
    @74
    cioo
    cF
    fvco3
    syl2an
    @85
    @90
    @87
    @88
    cop
    #
    cioo
    cfv
    @89
    @85
    @86
    @93
    cioo
    @85
    @86
    @22
    wcel
    @86
    @93
    wceq
    @85
    @23
    @22
    @86
    @82
    wph
    @81
    @91
    @86
    @23
    wcel
    @84
    uniioombl.1
    @92
    cn
    @23
    @74
    cF
    ffvelrn
    syl2an
    sseldi
    @86
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @87
    @88
    cioo
    df-ov
    syl6eqr
    eqtrd
    @87
    @88
    ioombl
    syl6eqel
    ralrimiva
    @67
    @75
    vn
    finiunmbl
    syl2anc
    eqeltrrd
    @37
    @44
    cL
    cK
    mblsplit
    syl3anc
    oveq1d
    eqtr4d
    breqtrd
    wph
    @54
    @12
    cC
    caddc
    co
    #
    cC
    caddc
    co
    @51
    cle
    wph
    @30
    @94
    cC
    @44
    wph
    @12
    cC
    uniioombl.e
    @48
    readdcld
    #
    @48
    wph
    @30
    @41
    @94
    @44
    @43
    @95
    wph
    @24
    @32
    @30
    @41
    cle
    wbr
    uniioombl.g
    @35
    cK
    cT
    cG
    uniioombl.t
    ovollb
    sylancl
    uniioombl.v
    letrd
    leadd1dd
    wph
    @12
    cC
    cC
    wph
    @12
    uniioombl.e
    recnd
    #
    @72
    @72
    addassd
    breqtrd
    letrd
    leadd1dd
    wph
    @52
    @12
    @10
    @10
    caddc
    co
    #
    caddc
    co
    @14
    wph
    @12
    @10
    @10
    @96
    wph
    @10
    @49
    recnd
    #
    @98
    addassd
    wph
    @13
    @97
    @12
    caddc
    wph
    @13
    c2
    c2
    cmul
    co
    #
    cC
    cmul
    co
    #
    @97
    @99
    c4
    cC
    cmul
    2t2e4
    oveq1i
    wph
    @100
    c2
    c2
    cC
    cmul
    co
    #
    cmul
    co
    c2
    @10
    cmul
    co
    @97
    wph
    c2
    c2
    cC
    wph
    2cnd
    #
    @102
    @72
    mulassd
    wph
    @101
    @10
    c2
    cmul
    wph
    cC
    @72
    2timesd
    oveq2d
    wph
    @10
    @98
    2timesd
    3eqtrd
    syl5eqr
    oveq2d
    eqtr4d
    breqtrd
    letrd
end
