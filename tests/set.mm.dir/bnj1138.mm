include "wcel.mm"
include "cun.mm"
include "wo.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"

theorem bnj1138
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  assume bnj1138.1: |- A = ( B u. C )


  assert |- ( X e. A <-> ( X e. B \/ X e. C ) )

  proof
    cX
    cA
    wcel
    cX
    cB
    cC
    cun
    #
    wcel
    cX
    cB
    wcel
    cX
    cC
    wcel
    wo
    cA
    @0
    cX
    bnj1138.1
    eleq2i
    cX
    cB
    cC
    elun
    bitri
end
