include "cin.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "r19.42v.mm"
include "elin.mm"
include "rexbii.mm"
include "eliun.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iunin2
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
  assert |- U_ x e. A ( B i^i C ) = ( B i^i U_ x e. A C )

  proof
    vy
    vx
    cA
    cB
    cC
    cin
    #
    ciun
    #
    cB
    vx
    cA
    cC
    ciun
    #
    cin
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    cB
    wcel
    #
    @4
    @2
    wcel
    #
    wa
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @7
    @4
    cC
    wcel
    #
    wa
    #
    vx
    cA
    wrex
    @7
    @10
    vx
    cA
    wrex
    #
    wa
    @6
    @9
    @7
    @10
    vx
    cA
    r19.42v
    @5
    @11
    vx
    cA
    @4
    cB
    cC
    elin
    rexbii
    @8
    @12
    @7
    vx
    @4
    cA
    cC
    eliun
    anbi2i
    3bitr4i
    vx
    @4
    cA
    @0
    eliun
    @4
    cB
    @2
    elin
    3bitr4i
    eqriv
end
