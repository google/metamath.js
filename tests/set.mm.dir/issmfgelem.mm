include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "csalg.mm"
include "restuni4.mm"
include "eqcomd.mm"
include "rabeqd.mm"
include "adantr.mm"
include "nfv.mm"
include "nfan.mm"
include "cvv.mm"
include "uniexd.mm"
include "simpr.mm"
include "ssexd.mm"
include "mpdan.mm"
include "eqid.mm"
include "subsalsal.mm"
include "cxr.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "adantlr.mm"
include "cle.mm"
include "eleq1d.mm"
include "ralbid.mm"
include "mpbid.mm"
include "rspa.mm"
include "syl2anc.mm"
include "salpreimagelt.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "issmf.mm"
include "mpbird.mm"

theorem issmfgelem
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume issmfgelem.x: |- F/ x ph
  assume issmfgelem.a: |- F/ a ph
  assume issmfgelem.s: |- ( ph -> S e. SAlg )
  assume issmfgelem.d: |- D = dom F
  assume issmfgelem.i: |- ( ph -> D C_ U. S )
  assume issmfgelem.f: |- ( ph -> F : D --> RR )
  assume issmfgelem.p: |- ( ph -> A. a e. RR { x e. D | a <_ ( F ` x ) } e. ( S |`t D ) )

  disjoint D a
  disjoint D x
  disjoint a x
  disjoint F a
  disjoint F x
  disjoint S a
  disjoint S x
  disjoint D b
  disjoint a b
  disjoint b x
  disjoint F b
  disjoint S b
  disjoint b ph
  disjoint k x
  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    cD
    cS
    cuni
    #
    wss
    #
    cD
    cr
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    clt
    wbr
    #
    vx
    cD
    crab
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    vb
    cr
    wral
    #
    w3a
    wph
    @1
    @2
    @10
    issmfgelem.i
    issmfgelem.f
    wph
    @9
    vb
    cr
    wph
    @5
    cr
    wcel
    #
    wa
    #
    @7
    @6
    vx
    @8
    cuni
    #
    crab
    #
    @8
    wph
    @7
    @14
    wceq
    @11
    wph
    @6
    vx
    cD
    @13
    wph
    @13
    cD
    wph
    cS
    cD
    csalg
    issmfgelem.s
    issmfgelem.i
    restuni4
    #
    eqcomd
    #
    rabeqd
    adantr
    @12
    vx
    @13
    @4
    @5
    @8
    va
    wph
    @11
    vx
    issmfgelem.x
    @11
    vx
    nfv
    nfan
    wph
    @11
    va
    issmfgelem.a
    @11
    va
    nfv
    nfan
    wph
    @8
    csalg
    wcel
    @11
    wph
    cD
    cS
    @8
    cvv
    issmfgelem.s
    wph
    @1
    cD
    cvv
    wcel
    issmfgelem.i
    wph
    @1
    wa
    cD
    @0
    cvv
    wph
    @0
    cvv
    wcel
    @1
    wph
    cS
    csalg
    issmfgelem.s
    uniexd
    adantr
    wph
    @1
    simpr
    ssexd
    mpdan
    @8
    eqid
    subsalsal
    adantr
    @13
    eqid
    wph
    @3
    @13
    wcel
    #
    @4
    cxr
    wcel
    @11
    wph
    @17
    wa
    #
    @4
    @18
    cD
    cr
    @3
    cF
    wph
    @2
    @17
    issmfgelem.f
    adantr
    @18
    @3
    @13
    cD
    wph
    @17
    simpr
    wph
    @13
    cD
    wceq
    @17
    @15
    adantr
    eleqtrd
    ffvelrnd
    rexrd
    adantlr
    wph
    va
    cv
    #
    cr
    wcel
    #
    @19
    @4
    cle
    wbr
    #
    vx
    @13
    crab
    #
    @8
    wcel
    #
    @11
    wph
    @20
    wa
    @23
    va
    cr
    wral
    #
    @20
    @23
    wph
    @24
    @20
    wph
    @21
    vx
    cD
    crab
    #
    @8
    wcel
    #
    va
    cr
    wral
    @24
    issmfgelem.p
    wph
    @26
    @23
    va
    cr
    issmfgelem.a
    wph
    @25
    @22
    @8
    wph
    @21
    vx
    cD
    @13
    @16
    rabeqd
    eleq1d
    ralbid
    mpbid
    adantr
    wph
    @20
    simpr
    @23
    va
    cr
    rspa
    syl2anc
    adantlr
    wph
    @11
    simpr
    salpreimagelt
    eqeltrd
    ralrimiva
    3jca
    wph
    vx
    cD
    cS
    cF
    vb
    issmfgelem.s
    issmfgelem.d
    issmf
    mpbird
end
