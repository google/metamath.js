include "crn.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wcel.mm"
include "elsni.mm"
include "fveq2d.mm"
include "mpteq2ia.mm"
include "a1i.mm"
include "feqmptd.mm"
include "cvv.mm"
include "fvexd.mm"
include "fmptsn.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "rneqd.mm"
include "rnsnopg.mm"
include "syl.mm"
include "eqtrd.mm"

theorem rnsnf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume rnsnf.1: |- ( ph -> A e. V )
  assume rnsnf.2: |- ( ph -> F : { A } --> B )


  assert |- ( ph -> ran F = { ( F ` A ) } )

  proof
    wph
    cF
    crn
    cA
    cA
    cF
    cfv
    #
    cop
    csn
    #
    crn
    #
    @0
    csn
    #
    wph
    cF
    @1
    wph
    vx
    cA
    csn
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    vx
    @4
    @0
    cmpt
    #
    cF
    @1
    @7
    @8
    wceq
    wph
    vx
    @4
    @6
    @0
    @5
    @4
    wcel
    @5
    cA
    cF
    @5
    cA
    elsni
    fveq2d
    mpteq2ia
    a1i
    wph
    vx
    @4
    cB
    cF
    rnsnf.2
    feqmptd
    wph
    cA
    cV
    wcel
    #
    @0
    cvv
    wcel
    @1
    @8
    wceq
    rnsnf.1
    wph
    cA
    cF
    fvexd
    vx
    cA
    @0
    cV
    cvv
    fmptsn
    syl2anc
    3eqtr4d
    rneqd
    wph
    @9
    @2
    @3
    wceq
    rnsnf.1
    cA
    @0
    cV
    rnsnopg
    syl
    eqtrd
end
