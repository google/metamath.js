include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
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
include "issmfgt.mm"
include "mpbid.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq1.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem smfpreimagt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume smfpreimagt.s: |- ( ph -> S e. SAlg )
  assume smfpreimagt.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpreimagt.d: |- D = dom F
  assume smfpreimagt.a: |- ( ph -> A e. RR )

  disjoint A x
  disjoint D x
  disjoint F x
  disjoint A a
  disjoint a x
  disjoint D a
  disjoint F a
  disjoint S a
  disjoint k x
  assert |- ( ph -> { x e. D | A < ( F ` x ) } e. ( S |`t D ) )

  proof
    wph
    cA
    cr
    wcel
    va
    cv
    #
    vx
    cv
    cF
    cfv
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
    va
    cr
    wral
    #
    cA
    @1
    clt
    wbr
    #
    vx
    cD
    crab
    #
    @4
    wcel
    #
    smfpreimagt.a
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
    smfpreimagt.f
    wph
    vx
    cD
    cS
    cF
    va
    smfpreimagt.s
    smfpreimagt.d
    issmfgt
    mpbid
    simp3d
    @5
    @9
    va
    cA
    cr
    @0
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
    @0
    cA
    @1
    clt
    breq1
    rabbidv
    eleq1d
    rspcva
    syl2anc
end
