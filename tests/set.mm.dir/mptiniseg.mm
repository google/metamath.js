include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "crab.mm"
include "wceq.mm"
include "mptpreima.mm"
include "elsn2g.mm"
include "rabbidv.mm"
include "syl5eq.mm"

theorem mptiniseg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vy: setvar y
  assume dmmpt.1: |- F = ( x e. A |-> B )

  disjoint C x
  disjoint V x
  disjoint x y
  disjoint C y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( C e. V -> ( `' F " { C } ) = { x e. A | B = C } )

  proof
    cC
    cV
    wcel
    #
    cF
    ccnv
    cC
    csn
    #
    cima
    cB
    @1
    wcel
    #
    vx
    cA
    crab
    cB
    cC
    wceq
    #
    vx
    cA
    crab
    vx
    cA
    cB
    @1
    cF
    dmmpt.1
    mptpreima
    @0
    @2
    @3
    vx
    cA
    cB
    cC
    cV
    elsn2g
    rabbidv
    syl5eq
end
