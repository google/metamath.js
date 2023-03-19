include "csslt.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "brsslt.mm"
include "simpr3.mm"
include "sylbi.mm"

theorem ssltsep
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( A <<s B -> A. x e. A A. y e. B x <s y )

  proof
    cA
    cB
    csslt
    wbr
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    cA
    csur
    wss
    #
    cB
    csur
    wss
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    vy
    cB
    wral
    vx
    cA
    wral
    #
    w3a
    wa
    @3
    vx
    vy
    cA
    cB
    brsslt
    @0
    @1
    @2
    @3
    simpr3
    sylbi
end
