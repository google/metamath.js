include "cint.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "elrint.mm"
include "baib.mm"

theorem elrint2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X

  disjoint B y
  disjoint X y
  assert |- ( X e. A -> ( X e. ( A i^i |^| B ) <-> A. y e. B X e. y ) )

  proof
    cX
    cA
    cB
    cint
    cin
    wcel
    cX
    cA
    wcel
    cX
    vy
    cv
    wcel
    vy
    cB
    wral
    vy
    cA
    cB
    cX
    elrint
    baib
end
