include "sseqin2.mm"

theorem sseqin2OLD
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( B i^i A ) = A )

  proof
    cA
    cB
    sseqin2
end
