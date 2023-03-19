include "cdif.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "r19.41v.mm"
include "eldif.mm"
include "rexbii.mm"
include "eliun.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iundif1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint C x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint C y
  assert |- U_ x e. A ( B \ C ) = ( U_ x e. A B \ C )

  proof
    vy
    vx
    cA
    cB
    cC
    cdif
    #
    ciun
    #
    vx
    cA
    cB
    ciun
    #
    cC
    cdif
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
    @2
    wcel
    #
    @4
    cC
    wcel
    wn
    #
    wa
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @4
    cB
    wcel
    #
    @8
    wa
    #
    vx
    cA
    wrex
    @10
    vx
    cA
    wrex
    #
    @8
    wa
    @6
    @9
    @10
    @8
    vx
    cA
    r19.41v
    @5
    @11
    vx
    cA
    @4
    cB
    cC
    eldif
    rexbii
    @7
    @12
    @8
    vx
    @4
    cA
    cB
    eliun
    anbi1i
    3bitr4i
    vx
    @4
    cA
    @0
    eliun
    @4
    @2
    cC
    eldif
    3bitr4i
    eqriv
end
