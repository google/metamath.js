include "crn.mm"
include "cc.mm"
include "wss.mm"
include "c1.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wral.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "csubmnd.mm"
include "ce.mm"
include "wa.mm"
include "wf.mm"
include "eff.mm"
include "a1i.mm"
include "adantr.mm"
include "csubg.mm"
include "cnfldbas.mm"
include "subgss.mm"
include "syl.mm"
include "sselda.mm"
include "mulcld.mm"
include "ffvelrnd.mm"
include "ralrimiva.mm"
include "rnmptss.mm"
include "cc0.mm"
include "mul01d.mm"
include "fveq2d.mm"
include "ef0.mm"
include "syl6eq.mm"
include "cvv.mm"
include "cnfld0.mm"
include "subg0cl.mm"
include "fvex.mm"
include "wceq.mm"
include "oveq2.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "w3a.mm"
include "cplusg.mm"
include "cbs.mm"
include "cgrp.mm"
include "cabl.mm"
include "efabl.mm"
include "ablgrp.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "cmpt.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "rnexg.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "3syl.mm"
include "oveqd.mm"
include "3eltr4d.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "crg.mm"
include "cmnd.mm"
include "wb.mm"
include "cnring.mm"
include "ringmgp.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "issubm.mm"
include "mp2b.mm"
include "syl3anbrc.mm"

theorem efsubm
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
  assert |- ( ph -> ran F e. ( SubMnd ` ( mulGrp ` CCfld ) ) )

  proof
    wph
    cF
    crn
    #
    cc
    wss
    #
    c1
    @0
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @0
    ccnfld
    cmgp
    cfv
    #
    csubmnd
    cfv
    wcel
    #
    wph
    cA
    @3
    cmul
    co
    #
    ce
    cfv
    #
    cc
    wcel
    #
    vx
    cX
    wral
    @1
    wph
    @12
    vx
    cX
    wph
    @3
    cX
    wcel
    #
    wa
    #
    cc
    cc
    @10
    ce
    cc
    cc
    ce
    wf
    @14
    eff
    a1i
    @14
    cA
    @3
    wph
    cA
    cc
    wcel
    @13
    efabl.3
    adantr
    wph
    cX
    cc
    @3
    wph
    cX
    ccnfld
    csubg
    cfv
    #
    wcel
    #
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
    @11
    cc
    cF
    efabl.1
    rnmptss
    syl
    #
    wph
    cA
    cc0
    cmul
    co
    #
    ce
    cfv
    #
    c1
    @0
    wph
    @19
    cc0
    ce
    cfv
    c1
    wph
    @18
    cc0
    ce
    wph
    cA
    efabl.3
    mul01d
    fveq2d
    ef0
    syl6eq
    wph
    cc0
    cX
    wcel
    #
    @19
    cvv
    wcel
    @19
    @0
    wcel
    wph
    @16
    @20
    efabl.4
    cX
    ccnfld
    cc0
    cnfld0
    subg0cl
    syl
    @18
    ce
    fvex
    vx
    cX
    @11
    @19
    cc0
    cF
    cvv
    efabl.1
    @3
    cc0
    wceq
    @10
    @18
    ce
    @3
    cc0
    cA
    cmul
    oveq2
    fveq2d
    elrnmpt1s
    sylancl
    eqeltrrd
    wph
    @6
    vx
    vy
    @0
    @0
    wph
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    @6
    wph
    @21
    @22
    w3a
    #
    @3
    @4
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    cbs
    cfv
    #
    @5
    @0
    @23
    cG
    cgrp
    wcel
    #
    @3
    @26
    wcel
    @4
    @26
    wcel
    @25
    @26
    wcel
    wph
    @21
    @27
    @22
    wph
    cG
    cabl
    wcel
    @27
    wph
    vx
    cA
    cF
    cG
    cX
    efabl.1
    efabl.2
    efabl.3
    efabl.4
    efabl
    cG
    ablgrp
    syl
    3ad2ant1
    @23
    @3
    @0
    @26
    wph
    @21
    @22
    simp2
    wph
    @21
    @0
    @26
    wceq
    #
    @22
    wph
    @1
    @28
    @17
    @0
    cc
    cG
    @8
    efabl.2
    cc
    ccnfld
    @8
    @8
    eqid
    #
    cnfldbas
    mgpbas
    #
    ressbas2
    syl
    3ad2ant1
    #
    eleqtrd
    @23
    @4
    @0
    @26
    wph
    @21
    @22
    simp3
    @31
    eleqtrd
    @26
    @24
    cG
    @3
    @4
    @26
    eqid
    @24
    eqid
    grpcl
    syl3anc
    @23
    cmul
    @24
    @3
    @4
    wph
    @21
    cmul
    @24
    wceq
    #
    @22
    wph
    cF
    cvv
    wcel
    @0
    cvv
    wcel
    @32
    wph
    cF
    vx
    cX
    @11
    cmpt
    #
    cvv
    efabl.1
    wph
    @16
    @33
    cvv
    wcel
    efabl.4
    vx
    cX
    @11
    @15
    mptexg
    syl
    syl5eqel
    cF
    cvv
    rnexg
    @0
    cmul
    @8
    cG
    cvv
    efabl.2
    ccnfld
    cmul
    @8
    @29
    cnfldmul
    mgpplusg
    #
    ressplusg
    3syl
    3ad2ant1
    oveqd
    @31
    3eltr4d
    3expb
    ralrimivva
    ccnfld
    crg
    wcel
    @8
    cmnd
    wcel
    @9
    @1
    @2
    @7
    w3a
    wb
    cnring
    ccnfld
    @8
    @29
    ringmgp
    vx
    vy
    cc
    cmul
    @0
    @8
    c1
    @30
    ccnfld
    c1
    @8
    @29
    cnfld1
    ringidval
    @34
    issubm
    mp2b
    syl3anbrc
end
