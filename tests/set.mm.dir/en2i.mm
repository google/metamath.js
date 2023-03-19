include "cen.mm"
include "wbr.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "en2d.mm"
include "trud.mm"

theorem en2i
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume en2i.1: |- A e. _V
  assume en2i.2: |- B e. _V
  assume en2i.3: |- ( x e. A -> C e. _V )
  assume en2i.4: |- ( y e. B -> D e. _V )
  assume en2i.5: |- ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) )

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
    en2i.1
    a1i
    cB
    cvv
    wcel
    wtru
    en2i.2
    a1i
    vx
    cv
    #
    cA
    wcel
    #
    cC
    cvv
    wcel
    wi
    wtru
    en2i.3
    a1i
    vy
    cv
    #
    cB
    wcel
    #
    cD
    cvv
    wcel
    wi
    wtru
    en2i.4
    a1i
    @1
    @2
    cC
    wceq
    wa
    @3
    @0
    cD
    wceq
    wa
    wb
    wtru
    en2i.5
    a1i
    en2d
    trud
end
