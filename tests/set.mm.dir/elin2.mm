include "wcel.mm"
include "cin.mm"
include "wa.mm"
include "eleq2i.mm"
include "elin.mm"
include "bitri.mm"

theorem elin2
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  assume elin2.x: |- X = ( B i^i C )


  assert |- ( A e. X <-> ( A e. B /\ A e. C ) )

  proof
    cA
    cX
    wcel
    cA
    cB
    cC
    cin
    #
    wcel
    cA
    cB
    wcel
    cA
    cC
    wcel
    wa
    cX
    @0
    cA
    elin2.x
    eleq2i
    cA
    cB
    cC
    elin
    bitri
end
