include "wss.mm"
include "wral.mm"
include "ciun.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"

theorem iunssd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iunssd.1: |- ( ( ph /\ x e. A ) -> B C_ C )

  disjoint C x
  disjoint ph x
  assert |- ( ph -> U_ x e. A B C_ C )

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
    ciun
    cC
    wss
    wph
    @0
    vx
    cA
    iunssd.1
    ralrimiva
    vx
    cA
    cB
    cC
    iunss
    sylibr
end
