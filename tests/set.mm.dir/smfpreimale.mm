include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wral.mm"
include "cuni.mm"
include "wss.mm"
include "wf.mm"
include "csmblfn.mm"
include "w3a.mm"
include "issmfle.mm"
include "mpbid.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem smfpreimale
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume smfpreimale.s: |- ( ph -> S e. SAlg )
  assume smfpreimale.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpreimale.d: |- D = dom F
  assume smfpreimale.a: |- ( ph -> A e. RR )

  disjoint A x
  disjoint D x
  disjoint F x
  disjoint A a
  disjoint a x
  disjoint D a
  disjoint F a
  disjoint S a
  disjoint k x
  assert |- ( ph -> { x e. D | ( F ` x ) <_ A } e. ( S |`t D ) )

  proof
    wph
    cA
    cr
    wcel
    vx
    cv
    cF
    cfv
    #
    va
    cv
    #
    cle
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
    va
    cr
    wral
    #
    @0
    cA
    cle
    wbr
    #
    vx
    cD
    crab
    #
    @4
    wcel
    #
    smfpreimale.a
    wph
    cD
    cS
    cuni
    wss
    #
    cD
    cr
    cF
    wf
    #
    @6
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    @10
    @11
    @6
    w3a
    smfpreimale.f
    wph
    vx
    cD
    cS
    cF
    va
    smfpreimale.s
    smfpreimale.d
    issmfle
    mpbid
    simp3d
    @5
    @9
    va
    cA
    cr
    @1
    cA
    wceq
    #
    @3
    @8
    @4
    @12
    @2
    @7
    vx
    cD
    @1
    cA
    @0
    cle
    breq2
    rabbidv
    eleq1d
    rspcva
    syl2anc
end
