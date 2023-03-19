include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "wn.mm"
include "c0.mm"
include "wnel.mm"
include "wb.mm"
include "df-nel.mm"
include "a1i.mm"
include "rabbiia.mm"
include "eqtri.mm"
include "ineq12i.mm"
include "rabnc.mm"

theorem elneldisjOLD
  let cA: class A
  let cB: class B
  let cE: class E
  let cN: class N
  let vs: setvar s
  assume elneldisjOLD.e: |- E = { s e. A | B e. s }
  assume elneldisjOLD.f: |- N = { s e. A | B e/ s }

  disjoint A s
  assert |- ( E i^i N ) = (/)

  proof
    cE
    cN
    cin
    cB
    vs
    cv
    #
    wcel
    #
    vs
    cA
    crab
    #
    @1
    wn
    #
    vs
    cA
    crab
    #
    cin
    c0
    cE
    @2
    cN
    @4
    elneldisjOLD.e
    cN
    cB
    @0
    wnel
    #
    vs
    cA
    crab
    @4
    elneldisjOLD.f
    @5
    @3
    vs
    cA
    @5
    @3
    wb
    @0
    cA
    wcel
    cB
    @0
    df-nel
    a1i
    rabbiia
    eqtri
    ineq12i
    @1
    vs
    cA
    rabnc
    eqtri
end
