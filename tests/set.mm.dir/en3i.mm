include "cen.mm"
include "wbr.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "cv.mm"
include "wi.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "en3d.mm"
include "trud.mm"

theorem en3i
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume en3i.1: |- A e. _V
  assume en3i.2: |- B e. _V
  assume en3i.3: |- ( x e. A -> C e. B )
  assume en3i.4: |- ( y e. B -> D e. A )
  assume en3i.5: |- ( ( x e. A /\ y e. B ) -> ( x = D <-> y = C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  assert |- A ~~ B

  proof
    cA
    cB
    cen
    wbr
    wtru
    vx
    vy
    cA
    cB
    cC
    cD
    cA
    cvv
    wcel
    wtru
    en3i.1
    a1i
    cB
    cvv
    wcel
    wtru
    en3i.2
    a1i
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
    wtru
    en3i.3
    a1i
    vy
    cv
    #
    cB
    wcel
    #
    cD
    cA
    wcel
    wi
    wtru
    en3i.4
    a1i
    @1
    @3
    wa
    @0
    cD
    wceq
    @2
    cC
    wceq
    wb
    wi
    wtru
    en3i.5
    a1i
    en3d
    trud
end
