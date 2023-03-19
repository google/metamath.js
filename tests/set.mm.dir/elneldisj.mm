include "cin.mm"
include "wcel.mm"
include "crab.mm"
include "wn.mm"
include "c0.mm"
include "wnel.mm"
include "df-nel.mm"
include "rabbii.mm"
include "eqtri.mm"
include "ineq12i.mm"
include "rabnc.mm"

theorem elneldisj
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cN: class N
  let vs: setvar s
  assume elneldisj.e: |- E = { s e. A | B e. C }
  assume elneldisj.n: |- N = { s e. A | B e/ C }

  disjoint A s
  assert |- ( E i^i N ) = (/)

  proof
    cE
    cN
    cin
    cB
    cC
    wcel
    #
    vs
    cA
    crab
    #
    @0
    wn
    #
    vs
    cA
    crab
    #
    cin
    c0
    cE
    @1
    cN
    @3
    elneldisj.e
    cN
    cB
    cC
    wnel
    #
    vs
    cA
    crab
    @3
    elneldisj.n
    @4
    @2
    vs
    cA
    cB
    cC
    df-nel
    rabbii
    eqtri
    ineq12i
    @0
    vs
    cA
    rabnc
    eqtri
end
