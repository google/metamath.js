include "cint.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "elin.mm"
include "elintg.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem elrint
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X

  disjoint B y
  disjoint X y
  assert |- ( X e. ( A i^i |^| B ) <-> ( X e. A /\ A. y e. B X e. y ) )

  proof
    cX
    cA
    cB
    cint
    #
    cin
    wcel
    cX
    cA
    wcel
    #
    cX
    @0
    wcel
    #
    wa
    @1
    cX
    vy
    cv
    wcel
    vy
    cB
    wral
    #
    wa
    cX
    cA
    @0
    elin
    @1
    @2
    @3
    vy
    cX
    cB
    cA
    elintg
    pm5.32i
    bitri
end
