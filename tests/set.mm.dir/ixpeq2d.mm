include "wceq.mm"
include "wral.mm"
include "cixp.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "ixpeq2.mm"
include "syl.mm"

theorem ixpeq2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ixpeq2d.1: |- F/ x ph
  assume ixpeq2d.2: |- ( ( ph /\ x e. A ) -> B = C )


  assert |- ( ph -> X_ x e. A B = X_ x e. A C )

  proof
    wph
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    vx
    cA
    cB
    cixp
    vx
    cA
    cC
    cixp
    wceq
    wph
    @0
    vx
    cA
    ixpeq2d.1
    wph
    vx
    cv
    cA
    wcel
    @0
    ixpeq2d.2
    ex
    ralrimi
    vx
    cA
    cB
    cC
    ixpeq2
    syl
end
