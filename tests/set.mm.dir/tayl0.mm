include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cc.mm"
include "ccnfld.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cz.mm"
include "cin.mm"
include "cv.mm"
include "cdvn.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cr.mm"
include "cpr.mm"
include "wss.mm"
include "recnprss.mm"
include "syl.mm"
include "sstrd.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "ralrimiva.mm"
include "cn0.mm"
include "cpnf.mm"
include "wo.mm"
include "cxnn0.mm"
include "elxnn0.mm"
include "cxr.mm"
include "cle.mm"
include "0xr.mm"
include "a1i.mm"
include "xnn0xr.mm"
include "xnn0ge0.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "sylbir.mm"
include "0zd.mm"
include "elind.mm"
include "rspcdva.mm"
include "cpm.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "dvn0.mm"
include "syl2anc.mm"
include "fdm.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "sseldd.mm"
include "cgsu.mm"
include "c1.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "crg.mm"
include "cmnd.mm"
include "cnring.mm"
include "ringmnd.mm"
include "mp1i.mm"
include "ovex.mm"
include "inex1.mm"
include "adantr.mm"
include "simpr.mm"
include "elin2d.mm"
include "w3a.mm"
include "elin1d.mm"
include "wb.mm"
include "nn0re.mm"
include "rexrd.mm"
include "id.mm"
include "pnfxr.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "elicc1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp2d.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "dvnf.mm"
include "ffvelrnd.mm"
include "faccld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "0cnd.mm"
include "expcld.mm"
include "mulcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "cn.mm"
include "eldifi.mm"
include "sylan2.mm"
include "eldifsni.mm"
include "adantl.mm"
include "elnnne0.mm"
include "0expd.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "zex.mm"
include "inex2.mm"
include "suppss2.mm"
include "gsumpt.mm"
include "fveq1d.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "0exp0e1.mm"
include "fvmpt.mm"
include "oveq1d.mm"
include "div1d.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "ctps.mm"
include "cnfldtps.mm"
include "wfun.mm"
include "cfn.mm"
include "csupp.mm"
include "cfsupp.mm"
include "mptexg.mm"
include "funmpt.mm"
include "c0ex.mm"
include "snfi.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "tsmsid.mm"
include "eqeltrrd.mm"
include "subidd.mm"
include "mpteq2dv.mm"
include "eleqtrrd.mm"
include "eltayl.mm"
include "mpbir2and.mm"
include "taylf.mm"
include "ffun.mm"
include "funbrfv2b.mm"
include "3syl.mm"

theorem tayl0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
  let cX: class X
  assume taylfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylfval.f: |- ( ph -> F : A --> CC )
  assume taylfval.a: |- ( ph -> A C_ S )
  assume taylfval.n: |- ( ph -> ( N e. NN0 \/ N = +oo ) )
  assume taylfval.b: |- ( ( ph /\ k e. ( ( 0 [,] N ) i^i ZZ ) ) -> B e. dom ( ( S Dn F ) ` k ) )
  assume taylfval.t: |- T = ( N ( S Tayl F ) B )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint N k
  disjoint S k
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a f
  disjoint a s
  disjoint F a
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint k s
  disjoint n s
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint f ph
  disjoint n ph
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint Y x
  disjoint N a
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S n
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint X k
  disjoint X x
  assert |- ( ph -> ( B e. dom T /\ ( T ` B ) = ( F ` B ) ) )

  proof
    wph
    cB
    cB
    cF
    cfv
    #
    cT
    wbr
    #
    cB
    cT
    cdm
    #
    wcel
    cB
    cT
    cfv
    @0
    wceq
    wa
    #
    wph
    @1
    cB
    cc
    wcel
    @0
    ccnfld
    vk
    cc0
    cN
    cicc
    co
    #
    cz
    cin
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @6
    cfa
    cfv
    #
    cdiv
    co
    #
    cB
    cB
    cmin
    co
    #
    @6
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    wcel
    wph
    cA
    cc
    cB
    wph
    cA
    cS
    cc
    taylfval.a
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cS
    cc
    wss
    #
    taylfval.s
    cS
    recnprss
    syl
    #
    sstrd
    wph
    cB
    cc0
    @7
    cfv
    #
    cdm
    #
    cA
    wph
    cB
    @8
    cdm
    #
    wcel
    #
    cB
    @22
    wcel
    vk
    @5
    cc0
    @6
    cc0
    wceq
    #
    @23
    @22
    cB
    @25
    @8
    @21
    @6
    cc0
    @7
    fveq2
    #
    dmeqd
    eleq2d
    wph
    @24
    vk
    @5
    taylfval.b
    ralrimiva
    wph
    @4
    cz
    cc0
    wph
    cN
    cn0
    wcel
    #
    cN
    cpnf
    wceq
    #
    wo
    #
    cc0
    @4
    wcel
    #
    taylfval.n
    @29
    cN
    cxnn0
    wcel
    #
    @30
    cN
    elxnn0
    @31
    cc0
    cxr
    wcel
    #
    cN
    cxr
    wcel
    #
    cc0
    cN
    cle
    wbr
    @30
    @32
    @31
    0xr
    a1i
    cN
    xnn0xr
    cN
    xnn0ge0
    cc0
    cN
    lbicc2
    syl3anc
    sylbir
    syl
    wph
    0zd
    elind
    #
    rspcdva
    wph
    @22
    cF
    cdm
    #
    cA
    wph
    @21
    cF
    wph
    @19
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    @21
    cF
    wceq
    @20
    wph
    cc
    cvv
    wcel
    #
    @18
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    @36
    @37
    wph
    cnex
    a1i
    taylfval.s
    taylfval.f
    taylfval.a
    cc
    cS
    cA
    cF
    cvv
    @17
    elpm2r
    syl22anc
    #
    cS
    cF
    dvn0
    syl2anc
    #
    dmeqd
    wph
    @38
    @35
    cA
    wceq
    taylfval.f
    cA
    cc
    cF
    fdm
    syl
    eqtrd
    eleqtrd
    #
    sseldd
    #
    wph
    @0
    ccnfld
    vk
    @5
    @11
    cc0
    @6
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    ctsu
    co
    #
    @16
    wph
    ccnfld
    @45
    cgsu
    co
    #
    @0
    @46
    wph
    @47
    cc0
    @45
    cfv
    #
    cB
    @21
    cfv
    #
    c1
    cdiv
    co
    #
    c1
    cmul
    co
    #
    @0
    wph
    @5
    cc
    @45
    ccnfld
    cvv
    cc0
    cc0
    cnfldbas
    cnfld0
    ccnfld
    crg
    wcel
    #
    ccnfld
    cmnd
    wcel
    wph
    cnring
    ccnfld
    ringmnd
    mp1i
    @5
    cvv
    wcel
    #
    wph
    @4
    cz
    cc0
    cN
    cicc
    ovex
    inex1
    a1i
    #
    @34
    wph
    vk
    @5
    @44
    cc
    @45
    wph
    @6
    @5
    wcel
    #
    wa
    #
    @11
    @43
    @56
    @9
    @10
    @56
    @23
    cc
    cB
    @8
    @56
    @18
    @36
    @6
    cn0
    wcel
    #
    @23
    cc
    @8
    wf
    wph
    @18
    @55
    taylfval.s
    adantr
    wph
    @36
    @55
    @39
    adantr
    @56
    @6
    cz
    wcel
    cc0
    @6
    cle
    wbr
    #
    @57
    @56
    @4
    cz
    @6
    wph
    @55
    simpr
    #
    elin2d
    @56
    @6
    cxr
    wcel
    #
    @58
    @6
    cN
    cle
    wbr
    #
    @56
    @6
    @4
    wcel
    #
    @60
    @58
    @61
    w3a
    #
    @56
    @4
    cz
    @6
    @59
    elin1d
    @56
    @32
    @33
    @62
    @63
    wb
    0xr
    wph
    @33
    @55
    wph
    @29
    @33
    taylfval.n
    @27
    @33
    @28
    @27
    cN
    cN
    nn0re
    rexrd
    @28
    cN
    cpnf
    cxr
    @28
    id
    pnfxr
    syl6eqel
    jaoi
    syl
    adantr
    cc0
    cN
    @6
    elicc1
    sylancr
    mpbid
    simp2d
    @6
    elnn0z
    sylanbrc
    #
    cS
    cF
    @6
    dvnf
    syl3anc
    taylfval.b
    ffvelrnd
    @56
    @10
    @56
    @6
    @64
    faccld
    #
    nncnd
    @56
    @10
    @65
    nnne0d
    divcld
    #
    @56
    cc0
    @6
    @56
    0cnd
    @64
    expcld
    mulcld
    @45
    eqid
    #
    fmptd
    #
    wph
    @5
    @44
    vk
    cvv
    cc0
    csn
    #
    cc0
    wph
    @6
    @5
    @69
    cdif
    wcel
    #
    wa
    #
    @44
    @11
    cc0
    cmul
    co
    #
    cc0
    @71
    @43
    cc0
    @11
    cmul
    @71
    @6
    @71
    @57
    @6
    cc0
    wne
    #
    @6
    cn
    wcel
    @70
    wph
    @55
    @57
    @6
    @5
    @69
    eldifi
    #
    @64
    sylan2
    @70
    @73
    wph
    @6
    @5
    cc0
    eldifsni
    adantl
    @6
    elnnne0
    sylanbrc
    0expd
    oveq2d
    @70
    wph
    @55
    @72
    cc0
    wceq
    @74
    @56
    @11
    @66
    mul01d
    sylan2
    eqtrd
    @53
    wph
    cz
    @4
    zex
    inex2
    #
    a1i
    suppss2
    #
    gsumpt
    wph
    cc0
    @5
    wcel
    @48
    @51
    wceq
    @34
    vk
    cc0
    @44
    @51
    @5
    @45
    @25
    @11
    @50
    @43
    c1
    cmul
    @25
    @9
    @49
    @10
    c1
    cdiv
    @25
    cB
    @8
    @21
    @26
    fveq1d
    @25
    @10
    cc0
    cfa
    cfv
    c1
    @6
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    oveq12d
    @25
    @43
    cc0
    cc0
    cexp
    co
    c1
    @6
    cc0
    cc0
    cexp
    oveq2
    0exp0e1
    syl6eq
    oveq12d
    @67
    @50
    c1
    cmul
    ovex
    fvmpt
    syl
    wph
    @51
    @0
    c1
    cmul
    co
    @0
    wph
    @50
    @0
    c1
    cmul
    wph
    @50
    @0
    c1
    cdiv
    co
    @0
    wph
    @49
    @0
    c1
    cdiv
    wph
    cB
    @21
    cF
    @40
    fveq1d
    oveq1d
    wph
    @0
    wph
    cA
    cc
    cB
    cF
    taylfval.f
    @41
    ffvelrnd
    #
    div1d
    eqtrd
    oveq1d
    wph
    @0
    @77
    mulid1d
    eqtrd
    3eqtrd
    wph
    @5
    cc
    @45
    ccnfld
    cvv
    cc0
    cnfldbas
    cnfld0
    @52
    ccnfld
    ccmn
    wcel
    wph
    cnring
    ccnfld
    ringcmn
    mp1i
    ccnfld
    ctps
    wcel
    wph
    cnfldtps
    a1i
    @54
    @68
    wph
    @45
    cvv
    wcel
    #
    @45
    wfun
    #
    cc0
    cvv
    wcel
    #
    @69
    cfn
    wcel
    #
    @45
    cc0
    csupp
    co
    @69
    wss
    @45
    cc0
    cfsupp
    wbr
    @53
    @78
    wph
    @75
    vk
    @5
    @44
    cvv
    mptexg
    mp1i
    @79
    wph
    vk
    @5
    @44
    funmpt
    a1i
    @80
    wph
    c0ex
    a1i
    @81
    wph
    cc0
    snfi
    a1i
    @76
    @69
    @45
    cvv
    cvv
    cc0
    suppssfifsupp
    syl32anc
    tsmsid
    eqeltrrd
    wph
    @15
    @45
    ccnfld
    ctsu
    wph
    vk
    @5
    @14
    @44
    wph
    @13
    @43
    @11
    cmul
    wph
    @12
    cc0
    @6
    cexp
    wph
    cB
    @42
    subidd
    oveq1d
    oveq2d
    mpteq2dv
    oveq2d
    eleqtrrd
    wph
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    cB
    @0
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfval.t
    eltayl
    mpbir2and
    wph
    @2
    cc
    cT
    wf
    cT
    wfun
    @1
    @3
    wb
    wph
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylfval.s
    taylfval.f
    taylfval.a
    taylfval.n
    taylfval.b
    taylfval.t
    taylf
    @2
    cc
    cT
    ffun
    cB
    @0
    cT
    funbrfv2b
    3syl
    mpbid
end
