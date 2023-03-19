include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "bitri.mm"
include "eqriv.mm"

theorem difeqri
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume difeqri.1: |- ( ( x e. A /\ -. x e. B ) <-> x e. C )

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A \ B ) = C

  proof
    vx
    cA
    cB
    cdif
    #
    cC
    vx
    cv
    #
    @0
    wcel
    @1
    cA
    wcel
    @1
    cB
    wcel
    wn
    wa
    @1
    cC
    wcel
    @1
    cA
    cB
    eldif
    difeqri.1
    bitri
    eqriv
end
