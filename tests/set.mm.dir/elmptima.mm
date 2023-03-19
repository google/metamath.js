include "wcel.mm"
include "cmpt.mm"
include "cima.mm"
include "cin.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "mptima.mm"
include "a1i.mm"
include "eleq2d.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "bitrd.mm"

theorem elmptima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( C e. V -> ( C e. ( ( x e. A |-> B ) " D ) <-> E. x e. ( A i^i D ) C = B ) )

  proof
    cC
    cV
    wcel
    #
    cC
    vx
    cA
    cB
    cmpt
    cD
    cima
    #
    wcel
    cC
    vx
    cA
    cD
    cin
    #
    cB
    cmpt
    #
    crn
    #
    wcel
    cC
    cB
    wceq
    vx
    @2
    wrex
    @0
    @1
    @4
    cC
    @1
    @4
    wceq
    @0
    vx
    cA
    cB
    cD
    mptima
    a1i
    eleq2d
    vx
    @2
    cB
    cC
    @3
    cV
    @3
    eqid
    elrnmpt
    bitrd
end
