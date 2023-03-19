include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"

theorem bnj931
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj931.1: |- A = ( B u. C )


  assert |- B C_ A

  proof
    cB
    cB
    cC
    cun
    cA
    cB
    cC
    ssun1
    bnj931.1
    sseqtr4i
end
