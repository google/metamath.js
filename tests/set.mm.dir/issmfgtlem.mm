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
include "r19.21bi.mm"
include "eqeltrd.mm"
include "salpreimagtlt.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "issmf.mm"
include "mpbird.mm"

theorem issmfgtlem
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume issmfgtlem.x: |- F/ x ph
  assume issmfgtlem.a: |- F/ a ph
  assume issmfgtlem.s: |- ( ph -> S e. SAlg )
  assume issmfgtlem.d: |- D = dom F
  assume issmfgtlem.i: |- ( ph -> D C_ U. S )
  assume issmfgtlem.f: |- ( ph -> F : D --> RR )
  assume issmfgtlem.p: |- ( ph -> A. a e. RR { x e. D | a < ( F ` x ) } e. ( S |`t D ) )

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
    issmfgtlem.i
    issmfgtlem.f
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
    issmfgtlem.s
    issmfgtlem.i
    restuni4
    #
    eqcomd
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
    issmfgtlem.x
    @11
    vx
    nfv
    nfan
    wph
    @11
    va
    issmfgtlem.a
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
    issmfgtlem.s
    wph
    @1
    cD
    cvv
    wcel
    issmfgtlem.i
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
    issmfgtlem.s
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
    @16
    wa
    #
    @4
    @17
    cD
    cr
    @3
    cF
    wph
    @2
    @16
    issmfgtlem.f
    adantr
    @17
    @3
    @13
    cD
    wph
    @16
    simpr
    wph
    @13
    cD
    wceq
    @16
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
    @18
    @4
    clt
    wbr
    #
    vx
    @13
    crab
    #
    @8
    wcel
    @11
    wph
    @19
    wa
    @21
    @20
    vx
    cD
    crab
    #
    @8
    wph
    @21
    @22
    wceq
    @19
    wph
    @20
    vx
    @13
    cD
    @15
    rabeqd
    adantr
    wph
    @22
    @8
    wcel
    va
    cr
    issmfgtlem.p
    r19.21bi
    eqeltrd
    adantlr
    wph
    @11
    simpr
    salpreimagtlt
    eqeltrd
    ralrimiva
    3jca
    wph
    vx
    cD
    cS
    cF
    vb
    issmfgtlem.s
    issmfgtlem.d
    issmf
    mpbird
end
