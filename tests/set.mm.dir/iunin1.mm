include "cin.mm"
include "ciun.mm"
include "iunin2.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "incom.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtr4i.mm"

theorem iunin1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  assert |- U_ x e. A ( C i^i B ) = ( U_ x e. A C i^i B )

  proof
    vx
    cA
    cB
    cC
    cin
    #
    ciun
    cB
    vx
    cA
    cC
    ciun
    #
    cin
    vx
    cA
    cC
    cB
    cin
    #
    ciun
    @1
    cB
    cin
    vx
    cA
    cB
    cC
    iunin2
    vx
    cA
    @2
    @0
    @2
    @0
    wceq
    vx
    cv
    cA
    wcel
    cC
    cB
    incom
    a1i
    iuneq2i
    @1
    cB
    incom
    3eqtr4i
end
