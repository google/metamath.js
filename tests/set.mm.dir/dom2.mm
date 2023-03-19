include "wceq.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "eqid.mm"
include "cv.mm"
include "a1i.mm"
include "wa.mm"
include "wb.mm"
include "dom2d.mm"
include "ax-mp.mm"

theorem dom2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  assume dom2.1: |- ( x e. A -> C e. B )
  assume dom2.2: |- ( ( x e. A /\ y e. A ) -> ( C = D <-> x = y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  assert |- ( B e. V -> A ~<_ B )

  proof
    cA
    cA
    wceq
    #
    cB
    cV
    wcel
    cA
    cB
    cdom
    wbr
    wi
    cA
    eqid
    @0
    vx
    vy
    cA
    cB
    cC
    cD
    cV
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
    @0
    dom2.1
    a1i
    @2
    vy
    cv
    #
    cA
    wcel
    wa
    cC
    cD
    wceq
    @1
    @3
    wceq
    wb
    wi
    @0
    dom2.2
    a1i
    dom2d
    ax-mp
end
