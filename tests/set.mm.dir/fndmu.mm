include "wfn.mm"
include "cdm.mm"
include "fndm.mm"
include "sylan9req.mm"

theorem fndmu
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ F Fn B ) -> A = B )

  proof
    cF
    cA
    wfn
    cF
    cB
    wfn
    cA
    cF
    cdm
    cB
    cA
    cF
    fndm
    cB
    cF
    fndm
    sylan9req
end
