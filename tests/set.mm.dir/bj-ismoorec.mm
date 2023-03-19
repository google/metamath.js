include "cmoore.mm"
include "wcel.mm"
include "cvv.mm"
include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "cpw.mm"
include "wral.mm"
include "elex.mm"
include "bj-ismoore.mm"
include "biadan2.mm"

theorem bj-ismoorec
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. Moore_ <-> ( A e. _V /\ A. x e. ~P A ( U. A i^i |^| x ) e. A ) )

  proof
    cA
    cmoore
    wcel
    cA
    cvv
    wcel
    cA
    cuni
    vx
    cv
    cint
    cin
    cA
    wcel
    vx
    cA
    cpw
    wral
    cA
    cmoore
    elex
    vx
    cA
    cvv
    bj-ismoore
    biadan2
end
