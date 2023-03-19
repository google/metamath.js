include "cin.mm"
include "ciun.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "iunin2.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "iunin1.mm"
include "eqtri.mm"

theorem 2iunin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint B x
  disjoint C y
  disjoint D x
  disjoint x y
  assert |- U_ x e. A U_ y e. B ( C i^i D ) = ( U_ x e. A C i^i U_ y e. B D )

  proof
    vx
    cA
    vy
    cB
    cC
    cD
    cin
    ciun
    #
    ciun
    vx
    cA
    cC
    vy
    cB
    cD
    ciun
    #
    cin
    #
    ciun
    vx
    cA
    cC
    ciun
    @1
    cin
    vx
    cA
    @0
    @2
    @0
    @2
    wceq
    vx
    cv
    cA
    wcel
    vy
    cB
    cC
    cD
    iunin2
    a1i
    iuneq2i
    vx
    cA
    @1
    cC
    iunin1
    eqtri
end
