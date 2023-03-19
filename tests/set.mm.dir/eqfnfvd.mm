include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem eqfnfvd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let cB: class B
  assume eqfnfvd.1: |- ( ph -> F Fn A )
  assume eqfnfvd.2: |- ( ph -> G Fn A )
  assume eqfnfvd.3: |- ( ( ph /\ x e. A ) -> ( F ` x ) = ( G ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint B x
  assert |- ( ph -> F = G )

  proof
    wph
    cF
    cG
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    @1
    cG
    cfv
    wceq
    #
    vx
    cA
    wral
    #
    wph
    @2
    vx
    cA
    eqfnfvd.3
    ralrimiva
    wph
    cF
    cA
    wfn
    cG
    cA
    wfn
    @0
    @3
    wb
    eqfnfvd.1
    eqfnfvd.2
    vx
    cA
    cF
    cG
    eqfnfv
    syl2anc
    mpbird
end
