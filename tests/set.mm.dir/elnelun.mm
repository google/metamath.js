include "cun.mm"
include "wcel.mm"
include "crab.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "rabbii.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "rabxm.mm"
include "eqtr4i.mm"

theorem elnelun
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cN: class N
  let vs: setvar s
  assume elneldisj.e: |- E = { s e. A | B e. C }
  assume elneldisj.n: |- N = { s e. A | B e/ C }

  disjoint A s
  assert |- ( E u. N ) = A

  proof
    cE
    cN
    cun
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
    cun
    cA
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
    uneq12i
    @0
    vs
    cA
    rabxm
    eqtr4i
end
