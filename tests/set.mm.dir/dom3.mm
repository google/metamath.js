include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "a1i.mm"
include "wceq.mm"
include "wb.mm"
include "simpl.mm"
include "simpr.mm"
include "dom3d.mm"

theorem dom3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  assume dom2.1: |- ( x e. A -> C e. B )
  assume dom2.2: |- ( ( x e. A /\ y e. A ) -> ( C = D <-> x = y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  assert |- ( ( A e. V /\ B e. W ) -> A ~<_ B )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cB
    cC
    cD
    cV
    cW
    vx
    cv
    #
    cA
    wcel
    #
    cC
    cB
    wcel
    wi
    @2
    dom2.1
    a1i
    @4
    vy
    cv
    #
    cA
    wcel
    wa
    cC
    cD
    wceq
    @3
    @5
    wceq
    wb
    wi
    @2
    dom2.2
    a1i
    @0
    @1
    simpl
    @0
    @1
    simpr
    dom3d
end
