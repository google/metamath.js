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
include "adantr.mm"
include "simpr.mm"
include "restuni4.mm"
include "eqcomd.mm"
include "mpdan.mm"
include "rabeqd.mm"
include "nfv.mm"
include "nfan.mm"
include "cvv.mm"
include "uniexd.mm"
include "ssexd.mm"
include "eqid.mm"
include "subsalsal.mm"
include "cxr.mm"
include "eleqtrd.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "rexrd.mm"
include "adantlr.mm"
include "cle.mm"
include "eqeltrd.mm"
include "salpreimalelt.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "issmf.mm"
include "mpbird.mm"

theorem issmflelem
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume issmflelem.x: |- F/ x ph
  assume issmflelem.a: |- F/ a ph
  assume issmflelem.s: |- ( ph -> S e. SAlg )
  assume issmflelem.d: |- D = dom F
  assume issmflelem.i: |- ( ph -> D C_ U. S )
  assume issmflelem.f: |- ( ph -> F : D --> RR )
  assume issmflelem.l: |- ( ( ph /\ a e. RR ) -> { x e. D | ( F ` x ) <_ a } e. ( S |`t D ) )

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
    issmflelem.i
    issmflelem.f
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
    @1
    cD
    @13
    wceq
    issmflelem.i
    wph
    @1
    wa
    #
    @13
    cD
    @15
    cS
    cD
    csalg
    wph
    cS
    csalg
    wcel
    @1
    issmflelem.s
    adantr
    #
    wph
    @1
    simpr
    #
    restuni4
    #
    eqcomd
    mpdan
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
    issmflelem.x
    @11
    vx
    nfv
    nfan
    wph
    @11
    va
    issmflelem.a
    @11
    va
    nfv
    nfan
    wph
    @8
    csalg
    wcel
    #
    @11
    wph
    @1
    @19
    issmflelem.i
    @15
    cD
    cS
    @8
    cvv
    @16
    @15
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
    issmflelem.s
    uniexd
    adantr
    @17
    ssexd
    @8
    eqid
    subsalsal
    mpdan
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
    @20
    wa
    #
    @4
    wph
    @20
    @3
    cD
    wcel
    @4
    cr
    wcel
    @21
    @3
    @13
    cD
    wph
    @20
    simpr
    wph
    @13
    cD
    wceq
    #
    @20
    wph
    @1
    @22
    issmflelem.i
    @18
    mpdan
    #
    adantr
    eleqtrd
    wph
    cD
    cr
    @3
    cF
    issmflelem.f
    ffvelrnda
    syldan
    rexrd
    adantlr
    wph
    va
    cv
    #
    cr
    wcel
    #
    @4
    @24
    cle
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
    @25
    wa
    @27
    @26
    vx
    cD
    crab
    #
    @8
    wph
    @27
    @28
    wceq
    @25
    wph
    @26
    vx
    @13
    cD
    @23
    rabeqd
    adantr
    issmflelem.l
    eqeltrd
    adantlr
    wph
    @11
    simpr
    salpreimalelt
    eqeltrd
    ralrimiva
    3jca
    wph
    vx
    cD
    cS
    cF
    vb
    issmflelem.s
    issmflelem.d
    issmf
    mpbird
end
