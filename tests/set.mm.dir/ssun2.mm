include "cun.mm"
include "ssun1.mm"
include "uncom.mm"
include "sseqtri.mm"

theorem ssun2
  let cA: class A
  let cB: class B


  assert |- A C_ ( B u. A )

  proof
    cA
    cA
    cB
    cun
    cB
    cA
    cun
    cA
    cB
    ssun1
    cA
    cB
    uncom
    sseqtri
end
