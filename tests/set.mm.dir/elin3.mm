include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "elin2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem elin3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  assume elin3.x: |- X = ( ( B i^i C ) i^i D )


  assert |- ( A e. X <-> ( A e. B /\ A e. C /\ A e. D ) )

  proof
    cA
    cB
    cC
    cin
    #
    wcel
    #
    cA
    cD
    wcel
    #
    wa
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wa
    #
    @2
    wa
    cA
    cX
    wcel
    @3
    @4
    @2
    w3a
    @1
    @5
    @2
    cA
    cB
    cC
    elin
    anbi1i
    cA
    @0
    cD
    cX
    elin3.x
    elin2
    @3
    @4
    @2
    df-3an
    3bitr4i
end
