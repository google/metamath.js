include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"

theorem ffrn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> F : A --> ran F )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cA
    cF
    crn
    cF
    wf
    cA
    cB
    cF
    ffn
    cA
    cF
    dffn3
    sylib
end
