include "cv.mm"
include "wtr.mm"
include "wral.mm"
include "ciun.mm"
include "cuni.mm"
include "triun.mm"
include "wceq.mm"
include "wb.mm"
include "uniiun.mm"
include "treq.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem truni
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. A Tr x -> Tr U. A )

  proof
    vx
    cv
    #
    wtr
    vx
    cA
    wral
    vx
    cA
    @0
    ciun
    #
    wtr
    #
    cA
    cuni
    #
    wtr
    #
    vx
    cA
    @0
    triun
    @3
    @1
    wceq
    @4
    @2
    wb
    vx
    cA
    uniiun
    @3
    @1
    treq
    ax-mp
    sylibr
end
