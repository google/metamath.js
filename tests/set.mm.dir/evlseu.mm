include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "crh.mm"
include "co.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "cbs.mm"
include "cfv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cmgp.mm"
include "cmg.mm"
include "cof.mm"
include "cgsu.mm"
include "cmulr.mm"
include "cmpt.mm"
include "w3a.mm"
include "eqid.mm"
include "evlslem1.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "3impb.mm"
include "syl.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wi.mm"
include "wral.mm"
include "wfun.mm"
include "csca.mm"
include "wf.mm"
include "cvv.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "mplring.mm"
include "mpllmod.mm"
include "asclf.mm"
include "syl2anc.mm"
include "ffun.mm"
include "funcoeqres.mm"
include "sylan.mm"
include "mvrf2.mm"
include "anim12dan.mm"
include "ex.mm"
include "resundi.mm"
include "uneq12.mm"
include "syl5eq.mm"
include "syl6.mm"
include "ralrimivw.mm"
include "weq.mm"
include "eqtr3.mm"
include "cin.mm"
include "cdm.mm"
include "wss.mm"
include "csubrg.mm"
include "cmrc.mm"
include "cmps.mm"
include "casp.mm"
include "cascl.mm"
include "casa.mm"
include "psrassa.mm"
include "mvrf.mm"
include "frn.mm"
include "aspval2.mm"
include "mplbas2.mm"
include "cpw.mm"
include "mplsubrg.mm"
include "mplval2.mm"
include "subsubrg2.mm"
include "fveq2d.mm"
include "ressascl.mm"
include "syl6reqr.mm"
include "rneqd.mm"
include "uneq1d.mm"
include "fveq12d.mm"
include "cmre.mm"
include "assaring.mm"
include "subrgmre.mm"
include "3syl.mm"
include "eqsstr3d.mm"
include "unssd.mm"
include "submrc.mm"
include "syl3anc.mm"
include "eqtr2d.mm"
include "3eqtr3d.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "rhmeql.mm"
include "ad2antlr.mm"
include "mrcsscl.mm"
include "eqsstrd.mm"
include "wfn.mm"
include "wb.mm"
include "simprl.mm"
include "rhmf.mm"
include "ffn.mm"
include "simprr.mm"
include "adantr.mm"
include "fnreseql.mm"
include "fneqeql2.mm"
include "3imtr4d.mm"
include "syl5.mm"
include "ralrimivva.mm"
include "reseq1.mm"
include "rmo4.mm"
include "sylibr.mm"
include "rmoim.mm"
include "sylc.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem evlseu
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume evlseu.p: |- P = ( I mPoly R )
  assume evlseu.c: |- C = ( Base ` S )
  assume evlseu.a: |- A = ( algSc ` P )
  assume evlseu.v: |- V = ( I mVar R )
  assume evlseu.i: |- ( ph -> I e. _V )
  assume evlseu.r: |- ( ph -> R e. CRing )
  assume evlseu.s: |- ( ph -> S e. CRing )
  assume evlseu.f: |- ( ph -> F e. ( R RingHom S ) )
  assume evlseu.g: |- ( ph -> G : I --> C )

  disjoint A m
  disjoint F m
  disjoint G m
  disjoint I m
  disjoint P m
  disjoint m ph
  disjoint S m
  disjoint V m
  disjoint m n
  disjoint A n
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint m z
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint V n
  assert |- ( ph -> E! m e. ( P RingHom S ) ( ( m o. A ) = F /\ ( m o. V ) = G ) )

  proof
    wph
    vm
    cv
    #
    cA
    ccom
    #
    cF
    wceq
    #
    @0
    cV
    ccom
    #
    cG
    wceq
    #
    wa
    #
    vm
    cP
    cS
    crh
    co
    #
    wrex
    #
    @5
    vm
    @6
    wrmo
    #
    @5
    vm
    @6
    wreu
    wph
    vx
    cP
    cbs
    cfv
    #
    cS
    vy
    vz
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vz
    cn0
    cI
    cmap
    co
    crab
    #
    vy
    cv
    #
    vx
    cv
    cfv
    cF
    cfv
    cS
    cmgp
    cfv
    #
    @11
    cG
    @12
    cmg
    cfv
    #
    cof
    co
    cgsu
    co
    cS
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    cmpt
    #
    @6
    wcel
    #
    @15
    cA
    ccom
    #
    cF
    wceq
    #
    @15
    cV
    ccom
    #
    cG
    wceq
    #
    w3a
    @7
    wph
    cA
    @9
    cC
    @10
    cP
    cR
    cS
    @12
    @14
    vz
    @15
    @13
    cF
    cG
    cI
    cR
    cbs
    cfv
    #
    cV
    vx
    vy
    evlseu.p
    @9
    eqid
    #
    evlseu.c
    @21
    eqid
    @10
    eqid
    @12
    eqid
    @13
    eqid
    @14
    eqid
    evlseu.v
    @15
    eqid
    evlseu.i
    evlseu.r
    evlseu.s
    evlseu.f
    evlseu.g
    evlseu.a
    evlslem1
    @16
    @18
    @20
    @7
    @5
    @18
    @20
    wa
    vm
    @15
    @6
    @0
    @15
    wceq
    #
    @2
    @18
    @4
    @20
    @23
    @1
    @17
    cF
    @0
    @15
    cA
    coeq1
    eqeq1d
    @23
    @3
    @19
    cG
    @0
    @15
    cV
    coeq1
    eqeq1d
    anbi12d
    rspcev
    3impb
    syl
    wph
    @5
    @0
    cA
    crn
    #
    cV
    crn
    #
    cun
    #
    cres
    #
    cF
    cA
    ccnv
    ccom
    #
    cG
    cV
    ccnv
    ccom
    #
    cun
    #
    wceq
    #
    wi
    #
    vm
    @6
    wral
    @31
    vm
    @6
    wrmo
    #
    @8
    wph
    @32
    vm
    @6
    wph
    @5
    @0
    @24
    cres
    #
    @28
    wceq
    #
    @0
    @25
    cres
    #
    @29
    wceq
    #
    wa
    #
    @31
    wph
    @5
    @38
    wph
    @2
    @35
    @4
    @37
    wph
    cA
    wfun
    #
    @2
    @35
    wph
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    @9
    cA
    wf
    #
    @39
    wph
    cI
    cvv
    wcel
    #
    cR
    crg
    wcel
    #
    @42
    evlseu.i
    wph
    cR
    ccrg
    wcel
    @44
    evlseu.r
    cR
    crngring
    syl
    #
    @43
    @44
    wa
    cA
    @9
    @40
    @41
    cP
    evlseu.a
    @40
    eqid
    cP
    cR
    cI
    cvv
    evlseu.p
    mplring
    #
    cP
    cR
    cI
    cvv
    evlseu.p
    mpllmod
    @41
    eqid
    @22
    asclf
    syl2anc
    #
    @41
    @9
    cA
    ffun
    syl
    @0
    cA
    cF
    funcoeqres
    sylan
    wph
    cV
    wfun
    #
    @4
    @37
    wph
    cI
    @9
    cV
    wf
    #
    @48
    wph
    @9
    cP
    cR
    cI
    cV
    cvv
    evlseu.p
    evlseu.v
    @22
    evlseu.i
    @45
    mvrf2
    #
    cI
    @9
    cV
    ffun
    syl
    @0
    cV
    cG
    funcoeqres
    sylan
    anim12dan
    ex
    @38
    @27
    @34
    @36
    cun
    @30
    @0
    @24
    @25
    resundi
    @34
    @28
    @36
    @29
    uneq12
    syl5eq
    syl6
    ralrimivw
    wph
    @31
    vn
    cv
    #
    @26
    cres
    #
    @30
    wceq
    #
    wa
    #
    vm
    vn
    weq
    #
    wi
    #
    vn
    @6
    wral
    vm
    @6
    wral
    @33
    wph
    @56
    vm
    vn
    @6
    @6
    @54
    @27
    @52
    wceq
    #
    wph
    @0
    @6
    wcel
    #
    @51
    @6
    wcel
    #
    wa
    #
    wa
    #
    @55
    @27
    @52
    @30
    eqtr3
    @61
    @26
    @0
    @51
    cin
    cdm
    #
    wss
    #
    @9
    @62
    wss
    #
    @57
    @55
    @61
    @63
    @64
    @61
    @63
    wa
    #
    @9
    @26
    cP
    csubrg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    @62
    wph
    @9
    @68
    wceq
    @60
    @63
    wph
    @25
    cI
    cR
    cmps
    co
    #
    casp
    cfv
    #
    cfv
    #
    @69
    cascl
    cfv
    #
    crn
    #
    @25
    cun
    #
    @69
    csubrg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    @9
    @68
    wph
    @69
    casa
    wcel
    #
    @25
    @69
    cbs
    cfv
    #
    wss
    #
    @71
    @77
    wceq
    wph
    cR
    @69
    cI
    cvv
    @69
    eqid
    #
    evlseu.i
    evlseu.r
    psrassa
    #
    wph
    cI
    @79
    cV
    wf
    @80
    wph
    @79
    cR
    @69
    cI
    cV
    cvv
    @81
    evlseu.v
    @79
    eqid
    #
    evlseu.i
    @45
    mvrf
    cI
    @79
    cV
    frn
    syl
    @70
    @72
    @76
    @25
    @79
    @69
    @70
    eqid
    #
    @72
    eqid
    #
    @76
    eqid
    #
    @83
    aspval2
    syl2anc
    wph
    @70
    cP
    cR
    @69
    cI
    cV
    cvv
    evlseu.p
    @81
    evlseu.v
    @84
    evlseu.i
    evlseu.r
    mplbas2
    wph
    @68
    @74
    @75
    @9
    cpw
    cin
    #
    cmrc
    cfv
    #
    cfv
    #
    @77
    wph
    @26
    @74
    @67
    @88
    wph
    @66
    @87
    cmrc
    wph
    @9
    @75
    wcel
    #
    @66
    @87
    wceq
    wph
    cP
    cR
    @69
    @9
    cI
    cvv
    @81
    evlseu.p
    @22
    evlseu.i
    @45
    mplsubrg
    #
    @9
    @69
    cP
    cP
    cR
    @69
    @9
    cI
    evlseu.p
    @81
    @22
    mplval2
    #
    subsubrg2
    syl
    fveq2d
    wph
    @24
    @73
    @25
    wph
    cA
    @72
    wph
    @72
    cP
    cascl
    cfv
    #
    cA
    wph
    @90
    @72
    @93
    wceq
    @91
    @72
    @9
    @69
    cP
    @85
    @92
    ressascl
    syl
    evlseu.a
    syl6reqr
    rneqd
    #
    uneq1d
    fveq12d
    wph
    @75
    @79
    cmre
    cfv
    wcel
    #
    @90
    @74
    @9
    wss
    @89
    @77
    wceq
    wph
    @78
    @69
    crg
    wcel
    @95
    @82
    @69
    assaring
    @79
    @69
    @83
    subrgmre
    3syl
    @91
    wph
    @73
    @25
    @9
    wph
    @73
    @24
    @9
    @94
    wph
    @42
    @24
    @9
    wss
    #
    @47
    @41
    @9
    cA
    frn
    syl
    #
    eqsstr3d
    wph
    @49
    @25
    @9
    wss
    #
    @50
    cI
    @9
    cV
    frn
    syl
    #
    unssd
    @75
    @9
    @74
    @76
    @88
    @79
    @86
    @88
    eqid
    submrc
    syl3anc
    eqtr2d
    3eqtr3d
    ad2antrr
    @65
    @66
    @9
    cmre
    cfv
    wcel
    #
    @63
    @62
    @66
    wcel
    #
    @68
    @62
    wss
    wph
    @100
    @60
    @63
    wph
    cP
    crg
    wcel
    #
    @100
    wph
    @43
    @44
    @102
    evlseu.i
    @45
    @46
    syl2anc
    @9
    cP
    @22
    subrgmre
    syl
    ad2antrr
    @61
    @63
    simpr
    @60
    @101
    wph
    @63
    cP
    cS
    @0
    @51
    rhmeql
    ad2antlr
    @66
    @26
    @67
    @62
    @9
    @67
    eqid
    mrcsscl
    syl3anc
    eqsstrd
    ex
    @61
    @0
    @9
    wfn
    #
    @51
    @9
    wfn
    #
    @26
    @9
    wss
    @57
    @63
    wb
    @61
    @58
    @9
    cC
    @0
    wf
    @103
    wph
    @58
    @59
    simprl
    @9
    cC
    cP
    cS
    @0
    @22
    evlseu.c
    rhmf
    @9
    cC
    @0
    ffn
    3syl
    #
    @61
    @59
    @9
    cC
    @51
    wf
    @104
    wph
    @58
    @59
    simprr
    @9
    cC
    cP
    cS
    @51
    @22
    evlseu.c
    rhmf
    @9
    cC
    @51
    ffn
    3syl
    #
    @61
    @24
    @25
    @9
    wph
    @96
    @60
    @97
    adantr
    wph
    @98
    @60
    @99
    adantr
    unssd
    @9
    @0
    @51
    @26
    fnreseql
    syl3anc
    @61
    @103
    @104
    @55
    @64
    wb
    @105
    @106
    @9
    @0
    @51
    fneqeql2
    syl2anc
    3imtr4d
    syl5
    ralrimivva
    @31
    @53
    vm
    vn
    @6
    @55
    @27
    @52
    @30
    @0
    @51
    @26
    reseq1
    eqeq1d
    rmo4
    sylibr
    @5
    @31
    vm
    @6
    rmoim
    sylc
    @5
    vm
    @6
    reu5
    sylanbrc
end
