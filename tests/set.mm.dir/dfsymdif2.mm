include "cv.mm"
include "wcel.mm"
include "wxo.mm"
include "csymdif.mm"
include "elsymdifxor.mm"
include "abbi2i.mm"

theorem dfsymdif2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A /_\ B ) = { x | ( x e. A \/_ x e. B ) }

  proof
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wxo
    vx
    cA
    cB
    csymdif
    @0
    cA
    cB
    elsymdifxor
    abbi2i
end
