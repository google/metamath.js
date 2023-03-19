include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "csubg.mm"
include "subgbas.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "wa.mm"
include "jca.mm"
include "efgh.mm"
include "syl3an1.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "crn.mm"
include "cvv.mm"
include "ce.mm"
include "cmpt.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "rnexg.mm"
include "3syl.mm"
include "cmgp.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "3eqtr3d.mm"
include "syl3anc.mm"
include "wfo.mm"
include "wfn.mm"
include "fvex.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "eqidd.mm"
include "wral.mm"
include "wss.mm"
include "wf.mm"
include "eff.mm"
include "a1i.mm"
include "adantr.mm"
include "cnfldbas.mm"
include "subgss.mm"
include "sselda.mm"
include "mulcld.mm"
include "ffvelrnd.mm"
include "ralrimiva.mm"
include "rnmptss.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "foeq123d.mm"
include "mpbii.mm"
include "cabl.mm"
include "crg.mm"
include "cnring.mm"
include "ringabl.mm"
include "ax-mp.mm"
include "subgabl.mm"
include "sylancr.mm"
include "ghmabl.mm"

theorem efabl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vy: setvar y
  assume efabl.1: |- F = ( x e. X |-> ( exp ` ( A x. x ) ) )
  assume efabl.2: |- G = ( ( mulGrp ` CCfld ) |`s ran F )
  assume efabl.3: |- ( ph -> A e. CC )
  assume efabl.4: |- ( ph -> X e. ( SubGrp ` CCfld ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint X x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint G y
  disjoint X y
  disjoint ph y
  assert |- ( ph -> G e. Abel )

  proof
    wph
    vx
    vy
    ccnfld
    cX
    cress
    co
    #
    cplusg
    cfv
    #
    cG
    cplusg
    cfv
    #
    cF
    @0
    cG
    @0
    cbs
    cfv
    #
    cG
    cbs
    cfv
    #
    @3
    eqid
    @4
    eqid
    @1
    eqid
    @2
    eqid
    wph
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    w3a
    #
    wph
    @5
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    @5
    @7
    @1
    co
    #
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    @2
    co
    #
    wceq
    wph
    @6
    @8
    simp1
    @9
    @5
    @3
    cX
    wph
    @6
    @8
    simp2
    wph
    @6
    cX
    @3
    wceq
    #
    @8
    wph
    cX
    ccnfld
    csubg
    cfv
    #
    wcel
    #
    @17
    efabl.4
    cX
    ccnfld
    @0
    @0
    eqid
    #
    subgbas
    syl
    #
    3ad2ant1
    #
    eleqtrrd
    @9
    @7
    @3
    cX
    wph
    @6
    @8
    simp3
    @22
    eleqtrrd
    wph
    @10
    @11
    w3a
    #
    @5
    @7
    caddc
    co
    #
    cF
    cfv
    #
    @14
    @15
    cmul
    co
    #
    @13
    @16
    wph
    cA
    cc
    wcel
    #
    @19
    wa
    @10
    @11
    @25
    @26
    wceq
    wph
    @27
    @19
    efabl.3
    efabl.4
    jca
    vx
    cA
    @5
    @7
    cF
    cX
    efabl.1
    efgh
    syl3an1
    @23
    @24
    @12
    cF
    @23
    caddc
    @1
    @5
    @7
    wph
    @10
    caddc
    @1
    wceq
    #
    @11
    wph
    @19
    @28
    efabl.4
    cX
    caddc
    ccnfld
    @0
    @18
    @20
    cnfldadd
    ressplusg
    syl
    3ad2ant1
    oveqd
    fveq2d
    @23
    cmul
    @2
    @14
    @15
    wph
    @10
    cmul
    @2
    wceq
    #
    @11
    wph
    cF
    crn
    #
    cvv
    wcel
    #
    @29
    wph
    @19
    cF
    cvv
    wcel
    @31
    efabl.4
    @19
    cF
    vx
    cX
    cA
    @5
    cmul
    co
    #
    ce
    cfv
    #
    cmpt
    cvv
    efabl.1
    vx
    cX
    @33
    @18
    mptexg
    syl5eqel
    cF
    cvv
    rnexg
    3syl
    @30
    cmul
    ccnfld
    cmgp
    cfv
    #
    cG
    cvv
    efabl.2
    ccnfld
    cmul
    @34
    @34
    eqid
    #
    cnfldmul
    mgpplusg
    ressplusg
    syl
    3ad2ant1
    oveqd
    3eqtr3d
    syl3anc
    wph
    cX
    @30
    cF
    wfo
    #
    @3
    @4
    cF
    wfo
    cF
    cX
    wfn
    @36
    vx
    cX
    @33
    cF
    @32
    ce
    fvex
    efabl.1
    fnmpti
    cX
    cF
    dffn4
    mpbi
    wph
    cX
    @3
    @30
    @4
    cF
    cF
    wph
    cF
    eqidd
    @21
    wph
    @33
    cc
    wcel
    #
    vx
    cX
    wral
    @30
    cc
    wss
    @30
    @4
    wceq
    wph
    @37
    vx
    cX
    wph
    @10
    wa
    #
    cc
    cc
    @32
    ce
    cc
    cc
    ce
    wf
    @38
    eff
    a1i
    @38
    cA
    @5
    wph
    @27
    @10
    efabl.3
    adantr
    wph
    cX
    cc
    @5
    wph
    @19
    cX
    cc
    wss
    efabl.4
    cc
    cX
    ccnfld
    cnfldbas
    subgss
    syl
    sselda
    mulcld
    ffvelrnd
    ralrimiva
    vx
    cX
    @33
    cc
    cF
    efabl.1
    rnmptss
    @30
    cc
    cG
    @34
    efabl.2
    cc
    ccnfld
    @34
    @35
    cnfldbas
    mgpbas
    ressbas2
    3syl
    foeq123d
    mpbii
    wph
    ccnfld
    cabl
    wcel
    #
    @19
    @0
    cabl
    wcel
    ccnfld
    crg
    wcel
    @39
    cnring
    ccnfld
    ringabl
    ax-mp
    efabl.4
    cX
    ccnfld
    @0
    @20
    subgabl
    sylancr
    ghmabl
end
