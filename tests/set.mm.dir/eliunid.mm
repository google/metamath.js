include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "ciun.mm"
include "rspe.mm"
include "eliun.mm"
include "sylibr.mm"

theorem eliunid
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- ( ( x e. A /\ C e. B ) -> C e. U_ x e. A B )

  proof
    vx
    cv
    cA
    wcel
    cC
    cB
    wcel
    #
    wa
    @0
    vx
    cA
    wrex
    cC
    vx
    cA
    cB
    ciun
    wcel
    @0
    vx
    cA
    rspe
    vx
    cC
    cA
    cB
    eliun
    sylibr
end
