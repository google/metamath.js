include "wss.mm"
include "wral.mm"
include "cixp.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "ss2ixp.mm"
include "syl.mm"

theorem ixpssixp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ixpssixp.1: |- F/ x ph
  assume ixpssixp.2: |- ( ( ph /\ x e. A ) -> B C_ C )


  assert |- ( ph -> X_ x e. A B C_ X_ x e. A C )

  proof
    wph
    cB
    cC
    wss
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
    wss
    wph
    @0
    vx
    cA
    ixpssixp.1
    wph
    vx
    cv
    cA
    wcel
    @0
    ixpssixp.2
    ex
    ralrimi
    vx
    cA
    cB
    cC
    ss2ixp
    syl
end
