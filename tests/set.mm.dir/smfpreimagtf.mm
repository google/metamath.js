include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "cdm.mm"
include "nfdm.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "smfpreimagt.mm"
include "eqeltrd.mm"

theorem smfpreimagtf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume smfpreimagtf.x: |- F/_ x F
  assume smfpreimagtf.s: |- ( ph -> S e. SAlg )
  assume smfpreimagtf.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpreimagtf.d: |- D = dom F
  assume smfpreimagtf.a: |- ( ph -> A e. RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint D y
  disjoint F y
  disjoint k x
  assert |- ( ph -> { x e. D | A < ( F ` x ) } e. ( S |`t D ) )

  proof
    wph
    cA
    vx
    cv
    #
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
    cA
    vy
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vy
    cD
    crab
    #
    cS
    cD
    crest
    co
    @3
    @7
    wceq
    wph
    @2
    @6
    vx
    vy
    cD
    vx
    cD
    cF
    cdm
    smfpreimagtf.d
    vx
    cF
    smfpreimagtf.x
    nfdm
    nfcxfr
    vy
    cD
    nfcv
    @2
    vy
    nfv
    vx
    cA
    @5
    clt
    vx
    cA
    nfcv
    vx
    clt
    nfcv
    vx
    @4
    cF
    smfpreimagtf.x
    vx
    @4
    nfcv
    nffv
    nfbr
    @0
    @4
    wceq
    @1
    @5
    cA
    clt
    @0
    @4
    cF
    fveq2
    breq2d
    cbvrab
    a1i
    wph
    vy
    cA
    cD
    cS
    cF
    smfpreimagtf.s
    smfpreimagtf.f
    smfpreimagtf.d
    smfpreimagtf.a
    smfpreimagt
    eqeltrd
end
