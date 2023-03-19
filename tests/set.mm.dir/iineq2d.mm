include "wceq.mm"
include "wral.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "iineq2.mm"
include "syl.mm"

theorem iineq2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iineq2d.1: |- F/ x ph
  assume iineq2d.2: |- ( ( ph /\ x e. A ) -> B = C )


  assert |- ( ph -> |^|_ x e. A B = |^|_ x e. A C )

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
    ciin
    vx
    cA
    cC
    ciin
    wceq
    wph
    @0
    vx
    cA
    iineq2d.1
    wph
    vx
    cv
    cA
    wcel
    @0
    iineq2d.2
    ex
    ralrimi
    vx
    cA
    cB
    cC
    iineq2
    syl
end
