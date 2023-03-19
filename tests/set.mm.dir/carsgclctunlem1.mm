include "cv.mm"
include "cuni.mm"
include "cin.mm"
include "cfv.mm"
include "cesum.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "unieq.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "esumeq1.mm"
include "eqeq12d.mm"
include "cc0.mm"
include "uni0.mm"
include "ineq2i.mm"
include "in0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "esumnul.mm"
include "3eqtr4g.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "simpr.mm"
include "eqcomd.mm"
include "simprr.mm"
include "cpw.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "adantr.mm"
include "elpwincl1.mm"
include "ffvelrnd.mm"
include "esumsn.mm"
include "oveq12d.mm"
include "nfv.mm"
include "nfcv.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "snex.mm"
include "wn.mm"
include "eldifbd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "esumsplit.mm"
include "inass.mm"
include "indir.mm"
include "inidm.mm"
include "incom.mm"
include "wdisj.mm"
include "adantrr.mm"
include "disjuniel.mm"
include "syl5eqr.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "indif2.mm"
include "uncom.mm"
include "difeq1i.mm"
include "disj3.mm"
include "biimpi.mm"
include "difun2.mm"
include "syl6reqr.mm"
include "syl.mm"
include "wral.mm"
include "ccarsg.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cle.mm"
include "3adant1r.mm"
include "cfn.mm"
include "ssfi.mm"
include "sylan.mm"
include "sstrd.mm"
include "fiunelcarsg.mm"
include "wb.mm"
include "elcarsg.mm"
include "mpbid.mm"
include "simprd.mm"
include "ineq1d.mm"
include "difeq1d.mm"
include "rspcdv.mm"
include "mpd.mm"
include "eqtr3d.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "findcard2d.mm"

theorem carsgclctunlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cE: class E
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let vb: setvar b
  let vf: setvar f
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume fiunelcarsg.1: |- ( ph -> A e. Fin )
  assume fiunelcarsg.2: |- ( ph -> A C_ ( toCaraSiga ` M ) )
  assume carsgclctunlem1.1: |- ( ph -> Disj_ y e. A y )
  assume carsgclctunlem1.2: |- ( ph -> E e. ~P O )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint E x
  disjoint E y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint M b
  disjoint M f
  disjoint O f
  disjoint b ph
  disjoint f ph
  assert |- ( ph -> ( M ` ( E i^i U. A ) ) = sum* y e. A ( M ` ( E i^i y ) ) )

  proof
    wph
    cE
    va
    cv
    #
    cuni
    #
    cin
    #
    cM
    cfv
    #
    @0
    cE
    vy
    cv
    #
    cin
    #
    cM
    cfv
    #
    vy
    cesum
    #
    wceq
    cE
    c0
    cuni
    #
    cin
    #
    cM
    cfv
    #
    c0
    @6
    vy
    cesum
    #
    wceq
    cE
    vb
    cv
    #
    cuni
    #
    cin
    #
    cM
    cfv
    #
    @12
    @6
    vy
    cesum
    #
    wceq
    #
    cE
    @12
    vx
    cv
    #
    csn
    #
    cun
    #
    cuni
    #
    cin
    #
    cM
    cfv
    #
    @20
    @6
    vy
    cesum
    #
    wceq
    #
    cE
    cA
    cuni
    #
    cin
    #
    cM
    cfv
    #
    cA
    @6
    vy
    cesum
    #
    wceq
    va
    vb
    vx
    cA
    @0
    c0
    wceq
    #
    @3
    @10
    @7
    @11
    @30
    @2
    @9
    cM
    @30
    @1
    @8
    cE
    @0
    c0
    unieq
    ineq2d
    fveq2d
    @0
    c0
    @6
    vy
    esumeq1
    eqeq12d
    @0
    @12
    wceq
    #
    @3
    @15
    @7
    @16
    @31
    @2
    @14
    cM
    @31
    @1
    @13
    cE
    @0
    @12
    unieq
    ineq2d
    fveq2d
    @0
    @12
    @6
    vy
    esumeq1
    eqeq12d
    @0
    @20
    wceq
    #
    @3
    @23
    @7
    @24
    @32
    @2
    @22
    cM
    @32
    @1
    @21
    cE
    @0
    @20
    unieq
    ineq2d
    fveq2d
    @0
    @20
    @6
    vy
    esumeq1
    eqeq12d
    @0
    cA
    wceq
    #
    @3
    @28
    @7
    @29
    @33
    @2
    @27
    cM
    @33
    @1
    @26
    cE
    @0
    cA
    unieq
    ineq2d
    fveq2d
    @0
    cA
    @6
    vy
    esumeq1
    eqeq12d
    wph
    c0
    cM
    cfv
    #
    cc0
    @10
    @11
    carsgsiga.1
    @9
    c0
    cM
    @9
    cE
    c0
    cin
    c0
    @8
    c0
    cE
    uni0
    ineq2i
    cE
    in0
    eqtri
    fveq2i
    vy
    @6
    esumnul
    3eqtr4g
    wph
    @12
    cA
    wss
    #
    @18
    cA
    @12
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    @17
    @25
    @39
    @17
    wa
    #
    @16
    @19
    @6
    vy
    cesum
    #
    cxad
    co
    #
    @15
    cE
    @18
    cin
    #
    cM
    cfv
    #
    cxad
    co
    #
    @24
    @23
    @40
    @16
    @15
    @41
    @44
    cxad
    @40
    @15
    @16
    @39
    @17
    simpr
    eqcomd
    @39
    @41
    @44
    wceq
    @17
    @39
    @6
    @44
    vy
    @18
    @36
    @39
    @4
    @18
    wceq
    #
    wa
    #
    @5
    @43
    cM
    @47
    @4
    @18
    cE
    @39
    @46
    simpr
    ineq2d
    fveq2d
    wph
    @35
    @37
    simprr
    #
    @39
    cO
    cpw
    #
    cc0
    cpnf
    cicc
    co
    #
    @43
    cM
    wph
    @49
    @50
    cM
    wf
    #
    @38
    carsgval.2
    adantr
    @39
    cE
    @18
    cO
    wph
    cE
    @49
    wcel
    #
    @38
    carsgclctunlem1.2
    adantr
    #
    elpwincl1
    ffvelrnd
    esumsn
    adantr
    oveq12d
    @39
    @24
    @42
    wceq
    @17
    @39
    @12
    @19
    @6
    vy
    @39
    vy
    nfv
    vy
    @12
    nfcv
    vy
    @19
    nfcv
    @12
    cvv
    wcel
    @39
    vb
    vex
    a1i
    @19
    cvv
    wcel
    @39
    @18
    snex
    a1i
    @39
    @18
    @12
    wcel
    wn
    @12
    @19
    cin
    c0
    wceq
    @39
    @18
    cA
    @12
    @48
    eldifbd
    @12
    @18
    disjsn
    sylibr
    @39
    @4
    @12
    wcel
    #
    wa
    #
    @49
    @50
    @5
    cM
    wph
    @51
    @38
    @54
    carsgval.2
    ad2antrr
    @55
    cE
    @4
    cO
    wph
    @52
    @38
    @54
    carsgclctunlem1.2
    ad2antrr
    elpwincl1
    ffvelrnd
    @39
    @4
    @19
    wcel
    #
    wa
    #
    @49
    @50
    @5
    cM
    wph
    @51
    @38
    @56
    carsgval.2
    ad2antrr
    @57
    cE
    @4
    cO
    wph
    @52
    @38
    @56
    carsgclctunlem1.2
    ad2antrr
    elpwincl1
    ffvelrnd
    esumsplit
    adantr
    @40
    @45
    cE
    @13
    @18
    cun
    #
    cin
    #
    cM
    cfv
    #
    @23
    @39
    @45
    @60
    wceq
    @17
    @39
    @59
    @13
    cin
    #
    cM
    cfv
    #
    @59
    @13
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @45
    @60
    @39
    @62
    @15
    @64
    @44
    cxad
    @39
    @61
    @14
    cM
    @39
    @61
    cE
    @58
    @13
    cin
    #
    cin
    @14
    cE
    @58
    @13
    inass
    @39
    @66
    @13
    cE
    @39
    @66
    @13
    @13
    cin
    #
    @18
    @13
    cin
    #
    cun
    #
    @13
    @13
    @18
    @13
    indir
    @39
    @69
    @13
    c0
    cun
    @13
    @39
    @67
    @13
    @68
    c0
    @67
    @13
    wceq
    @39
    @13
    inidm
    a1i
    @39
    @68
    @13
    @18
    cin
    c0
    @13
    @18
    incom
    @39
    vy
    cA
    @12
    @18
    wph
    vy
    cA
    @4
    wdisj
    @38
    carsgclctunlem1.1
    adantr
    wph
    @35
    @35
    @37
    wph
    @35
    simpr
    #
    adantrr
    @48
    disjuniel
    syl5eqr
    #
    uneq12d
    @13
    un0
    syl6eq
    syl5eq
    ineq2d
    syl5eq
    fveq2d
    @39
    @63
    @43
    cM
    @39
    @63
    cE
    @58
    @13
    cdif
    #
    cin
    @43
    cE
    @58
    @13
    indif2
    @39
    @72
    @18
    cE
    @39
    @68
    c0
    wceq
    #
    @72
    @18
    wceq
    @71
    @73
    @72
    @18
    @13
    cun
    #
    @13
    cdif
    #
    @18
    @58
    @74
    @13
    @13
    @18
    uncom
    difeq1i
    @73
    @18
    @18
    @13
    cdif
    #
    @75
    @73
    @18
    @76
    wceq
    @18
    @13
    disj3
    biimpi
    @18
    @13
    difun2
    syl6reqr
    syl5eq
    syl
    ineq2d
    syl5eqr
    fveq2d
    oveq12d
    @39
    ve
    cv
    #
    @13
    cin
    #
    cM
    cfv
    #
    @77
    @13
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @77
    cM
    cfv
    #
    wceq
    #
    ve
    @49
    wral
    #
    @65
    @60
    wceq
    #
    wph
    @35
    @85
    @37
    wph
    @35
    wa
    #
    @13
    cO
    wss
    #
    @85
    @87
    @13
    cM
    ccarsg
    cfv
    #
    wcel
    #
    @88
    @85
    wa
    #
    @87
    vx
    vy
    @12
    cM
    cO
    cV
    wph
    cO
    cV
    wcel
    @35
    carsgval.1
    adantr
    wph
    @51
    @35
    carsgval.2
    adantr
    wph
    @34
    cc0
    wceq
    @35
    carsgsiga.1
    adantr
    wph
    @18
    com
    cdom
    wbr
    @18
    @49
    wss
    @18
    cuni
    cM
    cfv
    @18
    @4
    cM
    cfv
    vy
    cesum
    cle
    wbr
    @35
    carsgsiga.2
    3adant1r
    wph
    cA
    cfn
    wcel
    @35
    @12
    cfn
    wcel
    fiunelcarsg.1
    cA
    @12
    ssfi
    sylan
    @87
    @12
    cA
    @89
    @70
    wph
    cA
    @89
    wss
    @35
    fiunelcarsg.2
    adantr
    sstrd
    fiunelcarsg
    wph
    @90
    @91
    wb
    @35
    wph
    @13
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    adantr
    mpbid
    simprd
    adantrr
    @39
    @84
    @86
    ve
    @59
    @49
    @39
    cE
    @58
    cO
    @53
    elpwincl1
    @39
    @77
    @59
    wceq
    #
    wa
    #
    @82
    @65
    @83
    @60
    @93
    @79
    @62
    @81
    @64
    cxad
    @93
    @78
    @61
    cM
    @93
    @77
    @59
    @13
    @39
    @92
    simpr
    #
    ineq1d
    fveq2d
    @93
    @80
    @63
    cM
    @93
    @77
    @59
    @13
    @94
    difeq1d
    fveq2d
    oveq12d
    @93
    @77
    @59
    cM
    @94
    fveq2d
    eqeq12d
    rspcdv
    mpd
    eqtr3d
    adantr
    @22
    @59
    cM
    @21
    @58
    cE
    @21
    @13
    @19
    cuni
    #
    cun
    @58
    @12
    @19
    uniun
    @95
    @18
    @13
    @18
    vx
    vex
    unisn
    uneq2i
    eqtri
    ineq2i
    fveq2i
    syl6reqr
    3eqtr4rd
    ex
    fiunelcarsg.1
    findcard2d
end
