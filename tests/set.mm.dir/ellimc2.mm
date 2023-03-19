include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "limccl.mm"
include "sseli.mm"
include "pm4.71ri.mm"
include "cun.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "crest.mm"
include "ccnp.mm"
include "wb.mm"
include "eqid.mm"
include "ellimc.mm"
include "adantr.mm"
include "ctopon.mm"
include "wf.mm"
include "cnfldtopon.mm"
include "snssd.mm"
include "unssd.mm"
include "resttopon.mm"
include "sylancr.mm"
include "a1i.mm"
include "ssun2.mm"
include "snssg.mm"
include "syl.mm"
include "mpbiri.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "simpllr.mm"
include "wn.mm"
include "pm5.61.mm"
include "ffvelrnda.mm"
include "ad2ant2r.mm"
include "sylan2b.mm"
include "anassrs.mm"
include "ifclda.mm"
include "fmptd.mm"
include "w3a.mm"
include "iscnp.mm"
include "baibd.mm"
include "syl31anc.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "sylan.mm"
include "eleq1d.mm"
include "imbi1d.mm"
include "crn.mm"
include "ctop.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "cnex.mm"
include "ssex.mm"
include "ad2antrr.mm"
include "restval.mm"
include "rexeqdv.mm"
include "vex.mm"
include "inex1.mm"
include "rgenw.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rexrnmpt.mm"
include "mp1i.mm"
include "ad3antrrr.mm"
include "elin.mm"
include "rbaib.mm"
include "wfn.mm"
include "fvex.mm"
include "ifexg.mm"
include "sylancl.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "fmpt.mm"
include "df-f.mm"
include "baib.mm"
include "3syl.mm"
include "simplrr.mm"
include "inss2.mm"
include "sylbi.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "undif1.mm"
include "ineq2i.mm"
include "indi.mm"
include "eqtr3i.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitr3d.mm"
include "wne.mm"
include "eldifsni.mm"
include "ifnefalse.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "cres.mm"
include "df-ima.mm"
include "resmpt.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "difss.mm"
include "sstri.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "3bitr4d.mm"
include "rexbidva.mm"
include "3bitrd.mm"
include "pm5.74da.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem ellimc2
  let wph: wff ph
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cK: class K
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  assume limccl.f: |- ( ph -> F : A --> CC )
  assume limccl.a: |- ( ph -> A C_ CC )
  assume limccl.b: |- ( ph -> B e. CC )
  assume ellimc2.k: |- K = ( TopOpen ` CCfld )

  disjoint u w
  disjoint A u
  disjoint A w
  disjoint B u
  disjoint B w
  disjoint ph u
  disjoint ph w
  disjoint C u
  disjoint C w
  disjoint F u
  disjoint F w
  disjoint K u
  disjoint K w
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A x
  disjoint A z
  disjoint u y
  disjoint v y
  disjoint B v
  disjoint w y
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph v
  disjoint ph x
  disjoint ph z
  disjoint C v
  disjoint C z
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint K v
  disjoint K z
  assert |- ( ph -> ( C e. ( F limCC B ) <-> ( C e. CC /\ A. u e. K ( C e. u -> E. w e. K ( B e. w /\ ( F " ( w i^i ( A \ { B } ) ) ) C_ u ) ) ) ) )

  proof
    cC
    cF
    cB
    climc
    co
    #
    wcel
    #
    cC
    cc
    wcel
    #
    @1
    wa
    wph
    @2
    cC
    vu
    cv
    #
    wcel
    #
    cB
    vw
    cv
    #
    wcel
    #
    cF
    @5
    cA
    cB
    csn
    #
    cdif
    #
    cin
    #
    cima
    @3
    wss
    #
    wa
    #
    vw
    cK
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wa
    @1
    @2
    @0
    cc
    cC
    cB
    cF
    limccl
    sseli
    pm4.71ri
    wph
    @2
    @1
    @14
    wph
    @2
    wa
    #
    @1
    vz
    cA
    @7
    cun
    #
    vz
    cv
    #
    cB
    wceq
    #
    cC
    @17
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cK
    @16
    crest
    co
    #
    cK
    ccnp
    co
    cfv
    wcel
    #
    cB
    @21
    cfv
    #
    @3
    wcel
    #
    cB
    vv
    cv
    #
    wcel
    #
    @21
    @26
    cima
    #
    @3
    wss
    #
    wa
    #
    vv
    @22
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    @14
    wph
    @1
    @23
    wb
    @2
    wph
    vz
    cA
    cB
    cC
    cF
    @21
    @22
    cK
    @22
    eqid
    ellimc2.k
    @21
    eqid
    #
    limccl.f
    limccl.a
    limccl.b
    ellimc
    adantr
    @15
    @22
    @16
    ctopon
    cfv
    wcel
    #
    cK
    cc
    ctopon
    cfv
    wcel
    #
    cB
    @16
    wcel
    #
    @16
    cc
    @21
    wf
    #
    @23
    @33
    wb
    wph
    @35
    @2
    wph
    @36
    @16
    cc
    wss
    #
    @35
    cK
    ellimc2.k
    cnfldtopon
    #
    wph
    cA
    @7
    cc
    limccl.a
    wph
    cB
    cc
    limccl.b
    snssd
    unssd
    #
    @16
    cK
    cc
    resttopon
    sylancr
    adantr
    @36
    @15
    @40
    a1i
    wph
    @37
    @2
    wph
    @37
    @7
    @16
    wss
    #
    @7
    cA
    ssun2
    wph
    cB
    cc
    wcel
    @37
    @42
    wb
    limccl.b
    cB
    @16
    cc
    snssg
    syl
    mpbiri
    #
    adantr
    @15
    vz
    @16
    @20
    cc
    @21
    @17
    @16
    wcel
    #
    @15
    @17
    cA
    wcel
    #
    @18
    wo
    #
    @20
    cc
    wcel
    @44
    @45
    @17
    @7
    wcel
    #
    wo
    @46
    @17
    cA
    @7
    elun
    @47
    @18
    @45
    vz
    cB
    velsn
    #
    orbi2i
    bitri
    @15
    @46
    wa
    @18
    cC
    @19
    cc
    wph
    @2
    @46
    @18
    simpllr
    @15
    @46
    @18
    wn
    #
    @19
    cc
    wcel
    #
    @46
    @49
    wa
    @15
    @45
    @49
    wa
    @50
    @45
    @18
    pm5.61
    wph
    @45
    @50
    @2
    @49
    wph
    cA
    cc
    @17
    cF
    limccl.f
    ffvelrnda
    ad2ant2r
    sylan2b
    anassrs
    ifclda
    sylan2b
    @34
    fmptd
    @35
    @36
    @37
    w3a
    @23
    @38
    @33
    vv
    vu
    cB
    @21
    @22
    cK
    @16
    cc
    iscnp
    baibd
    syl31anc
    @15
    @32
    @13
    vu
    cK
    @15
    @3
    cK
    wcel
    #
    wa
    #
    @32
    @4
    @31
    wi
    #
    @13
    @15
    @32
    @53
    wb
    @51
    @15
    @25
    @4
    @31
    @15
    @24
    cC
    @3
    wph
    @37
    @2
    @24
    cC
    wceq
    @43
    vz
    cB
    @20
    cC
    @16
    cc
    @21
    @18
    cC
    @19
    iftrue
    #
    @34
    fvmptg
    sylan
    eleq1d
    imbi1d
    adantr
    @52
    @4
    @31
    @12
    @15
    @51
    @4
    @31
    @12
    wb
    @15
    @51
    @4
    wa
    #
    wa
    #
    @31
    @30
    vv
    vw
    cK
    @5
    @16
    cin
    #
    cmpt
    #
    crn
    #
    wrex
    #
    cB
    @57
    wcel
    #
    @21
    @57
    cima
    #
    @3
    wss
    #
    wa
    #
    vw
    cK
    wrex
    #
    @12
    @56
    @30
    vv
    @22
    @59
    @56
    cK
    ctop
    wcel
    @16
    cvv
    wcel
    #
    @22
    @59
    wceq
    cK
    ellimc2.k
    cnfldtop
    wph
    @66
    @2
    @55
    wph
    @39
    @66
    @41
    @16
    cc
    cnex
    ssex
    syl
    ad2antrr
    vw
    @16
    cK
    ctop
    cvv
    restval
    sylancr
    rexeqdv
    @57
    cvv
    wcel
    #
    vw
    cK
    wral
    @60
    @65
    wb
    @56
    @67
    vw
    cK
    @5
    @16
    vw
    vex
    inex1
    rgenw
    @30
    @64
    vw
    vv
    cK
    @57
    @58
    cvv
    @58
    eqid
    @26
    @57
    wceq
    #
    @27
    @61
    @29
    @63
    @26
    @57
    cB
    eleq2
    @68
    @28
    @62
    @3
    @26
    @57
    @21
    imaeq2
    sseq1d
    anbi12d
    rexrnmpt
    mp1i
    @56
    @64
    @11
    vw
    cK
    @56
    @5
    cK
    wcel
    #
    wa
    #
    @61
    @6
    @63
    @10
    @70
    @37
    @61
    @6
    wb
    wph
    @37
    @2
    @55
    @69
    @43
    ad3antrrr
    @61
    @6
    @37
    cB
    @5
    @16
    elin
    rbaib
    syl
    @70
    vz
    @57
    @20
    cmpt
    #
    crn
    #
    @3
    wss
    #
    @19
    @3
    wcel
    #
    vz
    @9
    wral
    #
    @63
    @10
    @70
    @73
    @20
    @3
    wcel
    #
    vz
    @9
    wral
    #
    @75
    @70
    @76
    vz
    @57
    wral
    #
    @73
    @77
    @70
    @20
    cvv
    wcel
    #
    vz
    @57
    wral
    @71
    @57
    wfn
    #
    @78
    @73
    wb
    @70
    @79
    vz
    @57
    @70
    @2
    @19
    cvv
    wcel
    @79
    wph
    @2
    @55
    @69
    simpllr
    @17
    cF
    fvex
    @18
    cC
    @19
    cc
    cvv
    ifexg
    sylancl
    ralrimivw
    vz
    @57
    @20
    @71
    cvv
    @71
    eqid
    #
    fnmpt
    @78
    @80
    @73
    @78
    @57
    @3
    @71
    wf
    @80
    @73
    wa
    vz
    @57
    @3
    @20
    @71
    @81
    fmpt
    @57
    @3
    @71
    df-f
    bitri
    baib
    3syl
    @70
    @76
    vz
    @5
    @7
    cin
    #
    wral
    #
    @78
    @77
    wb
    @70
    @76
    vz
    @82
    @70
    @76
    @17
    @82
    wcel
    #
    @4
    @15
    @51
    @4
    @69
    simplrr
    @84
    @47
    @76
    @4
    wb
    @82
    @7
    @17
    @5
    @7
    inss2
    sseli
    @47
    @20
    cC
    @3
    @47
    @18
    @20
    cC
    wceq
    @48
    @54
    sylbi
    eleq1d
    syl
    syl5ibrcom
    ralrimiv
    @78
    @77
    @83
    @78
    @76
    vz
    @9
    @82
    cun
    #
    wral
    @77
    @83
    wa
    @76
    vz
    @57
    @85
    @5
    @8
    @7
    cun
    #
    cin
    @57
    @85
    @86
    @16
    @5
    cA
    @7
    undif1
    ineq2i
    @5
    @8
    @7
    indi
    eqtr3i
    raleqi
    @76
    vz
    @9
    @82
    ralunb
    bitri
    rbaib
    syl
    bitr3d
    @76
    @74
    vz
    @9
    @17
    @9
    wcel
    @17
    @8
    wcel
    #
    @76
    @74
    wb
    @9
    @8
    @17
    @5
    @8
    inss2
    #
    sseli
    @87
    @20
    @19
    @3
    @87
    @17
    cB
    wne
    @20
    @19
    wceq
    @17
    cA
    cB
    eldifsni
    @17
    cB
    cC
    @19
    ifnefalse
    syl
    eleq1d
    syl
    ralbiia
    syl6bb
    @70
    @62
    @72
    @3
    @70
    @62
    @21
    @57
    cres
    #
    crn
    @72
    @21
    @57
    df-ima
    @70
    @89
    @71
    @57
    @16
    wss
    @89
    @71
    wceq
    @70
    @5
    @16
    inss2
    vz
    @16
    @57
    @20
    resmpt
    mp1i
    rneqd
    syl5eq
    sseq1d
    @70
    cF
    wfun
    #
    @9
    cF
    cdm
    #
    wss
    @10
    @75
    wb
    @70
    cA
    cc
    cF
    wf
    #
    @90
    wph
    @92
    @2
    @55
    @69
    limccl.f
    ad3antrrr
    #
    cA
    cc
    cF
    ffun
    syl
    @70
    cA
    @9
    @91
    @9
    @8
    cA
    @88
    cA
    @7
    difss
    sstri
    @70
    @92
    @91
    cA
    wceq
    @93
    cA
    cc
    cF
    fdm
    syl
    syl5sseqr
    vz
    @9
    @3
    cF
    funimass4
    syl2anc
    3bitr4d
    anbi12d
    rexbidva
    3bitrd
    anassrs
    pm5.74da
    bitrd
    ralbidva
    3bitrd
    pm5.32da
    syl5bb
end
