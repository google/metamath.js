include "cdprd.mm"
include "co.mm"
include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cixp.mm"
include "crab.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "cdm.mm"
include "wceq.mm"
include "eqid.mm"
include "dprdval.mm"
include "syl2anc.mm"
include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "ccntz.mm"
include "cgrp.mm"
include "cmnd.mm"
include "adantr.mm"
include "dprdgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "dprddomcld.mm"
include "csubg.mm"
include "csubmnd.mm"
include "subgsubm.mm"
include "syl.mm"
include "wfn.mm"
include "wral.mm"
include "cbs.mm"
include "simpr.mm"
include "dprdff.mm"
include "ffn.mm"
include "adantlr.mm"
include "dprdfcl.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "dprdfcntz.mm"
include "dprdffsupp.mm"
include "gsumzsubmcl.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"

theorem dprdlub
  let wph: wff ph
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  assume dprdlub.1: |- ( ph -> G dom DProd S )
  assume dprdlub.2: |- ( ph -> dom S = I )
  assume dprdlub.3: |- ( ph -> T e. ( SubGrp ` G ) )
  assume dprdlub.4: |- ( ( ph /\ k e. I ) -> ( S ` k ) C_ T )

  disjoint G k
  disjoint I k
  disjoint k ph
  disjoint S k
  disjoint T k
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint G f
  disjoint h i
  disjoint h k
  disjoint G h
  disjoint i k
  disjoint G i
  disjoint I f
  disjoint I h
  disjoint I i
  disjoint f ph
  disjoint S f
  disjoint S h
  disjoint S i
  disjoint T f
  assert |- ( ph -> ( G DProd S ) C_ T )

  proof
    wph
    cG
    cS
    cdprd
    co
    #
    vf
    vh
    cv
    cG
    c0g
    cfv
    #
    cfsupp
    wbr
    vh
    vi
    cI
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    cG
    vf
    cv
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cT
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    cS
    cdm
    cI
    wceq
    #
    @0
    @6
    wceq
    dprdlub.1
    dprdlub.2
    cS
    vf
    vh
    vi
    cG
    cI
    @2
    @1
    @1
    eqid
    #
    @2
    eqid
    #
    dprdval
    syl2anc
    wph
    @2
    cT
    @5
    wf
    @6
    cT
    wss
    wph
    vf
    @2
    @4
    cT
    @5
    wph
    @3
    @2
    wcel
    #
    wa
    #
    cI
    cT
    @3
    cG
    cvv
    @1
    cG
    ccntz
    cfv
    #
    @9
    @13
    eqid
    #
    @12
    @7
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    wph
    @7
    @11
    dprdlub.1
    adantr
    #
    cS
    cG
    dprdgrp
    cG
    grpmnd
    3syl
    wph
    cI
    cvv
    wcel
    @11
    wph
    cS
    cG
    cI
    dprdlub.1
    dprdlub.2
    dprddomcld
    adantr
    @12
    cT
    cG
    csubg
    cfv
    wcel
    #
    cT
    cG
    csubmnd
    cfv
    wcel
    wph
    @16
    @11
    dprdlub.3
    adantr
    cT
    cG
    subgsubm
    syl
    @12
    @3
    cI
    wfn
    #
    vk
    cv
    #
    @3
    cfv
    #
    cT
    wcel
    #
    vk
    cI
    wral
    cI
    cT
    @3
    wf
    @12
    cI
    cG
    cbs
    cfv
    #
    @3
    wf
    @17
    @12
    @21
    cS
    vh
    vi
    @3
    cG
    cI
    @2
    @1
    @10
    @15
    wph
    @8
    @11
    dprdlub.2
    adantr
    #
    wph
    @11
    simpr
    #
    @21
    eqid
    dprdff
    cI
    @21
    @3
    ffn
    syl
    @12
    @20
    vk
    cI
    @12
    @18
    cI
    wcel
    #
    wa
    @18
    cS
    cfv
    #
    cT
    @19
    wph
    @24
    @25
    cT
    wss
    @11
    dprdlub.4
    adantlr
    @12
    cS
    vh
    vi
    @3
    cG
    cI
    @2
    @18
    @1
    @10
    @15
    @22
    @23
    dprdfcl
    sseldd
    ralrimiva
    vk
    cI
    cT
    @3
    ffnfv
    sylanbrc
    @12
    cS
    vh
    vi
    @3
    cG
    cI
    @2
    @1
    @13
    @10
    @15
    @22
    @23
    @14
    dprdfcntz
    @12
    cS
    vh
    vi
    @3
    cG
    cI
    @2
    @1
    @10
    @15
    @22
    @23
    dprdffsupp
    gsumzsubmcl
    @5
    eqid
    fmptd
    @2
    cT
    @5
    frn
    syl
    eqsstrd
end
