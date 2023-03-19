include "wceq.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "iuneq2.mm"
include "syl.mm"

theorem iuneq2df
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2df.1: |- F/ x ph
  assume iuneq2df.2: |- ( ( ph /\ x e. A ) -> B = C )


  assert |- ( ph -> U_ x e. A B = U_ x e. A C )

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
    ciun
    vx
    cA
    cC
    ciun
    wceq
    wph
    @0
    vx
    cA
    iuneq2df.1
    wph
    vx
    cv
    cA
    wcel
    @0
    iuneq2df.2
    ex
    ralrimi
    vx
    cA
    cB
    cC
    iuneq2
    syl
end
