include "cun.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wo.mm"
include "r19.32v.mm"
include "elun.mm"
include "ralbii.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "orbi2i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iinun2
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
  assert |- |^|_ x e. A ( B u. C ) = ( B u. |^|_ x e. A C )

  proof
    vy
    vx
    cA
    cB
    cC
    cun
    #
    ciin
    #
    cB
    vx
    cA
    cC
    ciin
    #
    cun
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wral
    #
    @4
    cB
    wcel
    #
    @4
    @2
    wcel
    #
    wo
    #
    @4
    @1
    wcel
    #
    @4
    @3
    wcel
    @7
    @4
    cC
    wcel
    #
    wo
    #
    vx
    cA
    wral
    @7
    @11
    vx
    cA
    wral
    #
    wo
    @6
    @9
    @7
    @11
    vx
    cA
    r19.32v
    @5
    @12
    vx
    cA
    @4
    cB
    cC
    elun
    ralbii
    @8
    @13
    @7
    @4
    cvv
    wcel
    #
    @8
    @13
    wb
    vy
    vex
    #
    vx
    @4
    cA
    cC
    cvv
    eliin
    ax-mp
    orbi2i
    3bitr4i
    @14
    @10
    @6
    wb
    @15
    vx
    @4
    cA
    @0
    cvv
    eliin
    ax-mp
    @4
    cB
    @2
    elun
    3bitr4i
    eqriv
end
