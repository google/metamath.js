include "ciin.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "eliin.mm"
include "syl.mm"
include "mpbird.mm"

theorem eliind2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume eliind2.1: |- F/ x ph
  assume eliind2.2: |- ( ph -> A e. V )
  assume eliind2.3: |- ( ( ph /\ x e. B ) -> A e. C )

  disjoint A x
  assert |- ( ph -> A e. |^|_ x e. B C )

  proof
    wph
    cA
    vx
    cB
    cC
    ciin
    wcel
    #
    cA
    cC
    wcel
    #
    vx
    cB
    wral
    #
    wph
    @1
    vx
    cB
    eliind2.1
    wph
    vx
    cv
    cB
    wcel
    @1
    eliind2.3
    ex
    ralrimi
    wph
    cA
    cV
    wcel
    @0
    @2
    wb
    eliind2.2
    vx
    cA
    cB
    cC
    cV
    eliin
    syl
    mpbird
end
