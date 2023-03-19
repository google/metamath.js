include "crn.mm"
include "c0.mm"
include "wceq.mm"
include "neneqd.mm"
include "rnmpt0.mm"
include "mtbird.mm"
include "neqned.mm"

theorem rnmptn0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  assume rnmptn0.x: |- F/ x ph
  assume rnmptn0.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume rnmptn0.f: |- F = ( x e. A |-> B )
  assume rnmptn0.a: |- ( ph -> A =/= (/) )

  disjoint A x
  assert |- ( ph -> ran F =/= (/) )

  proof
    wph
    cF
    crn
    #
    c0
    wph
    @0
    c0
    wceq
    cA
    c0
    wceq
    wph
    cA
    c0
    rnmptn0.a
    neneqd
    wph
    vx
    cA
    cB
    cF
    cV
    rnmptn0.x
    rnmptn0.b
    rnmptn0.f
    rnmpt0
    mtbird
    neqned
end
