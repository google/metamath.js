include "wfn.mm"
include "cres.mm"
include "wss.mm"
include "fnssresb.mm"
include "biimpar.mm"

theorem fnssres
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ B C_ A ) -> ( F |` B ) Fn B )

  proof
    cF
    cA
    wfn
    cF
    cB
    cres
    cB
    wfn
    cB
    cA
    wss
    cA
    cB
    cF
    fnssresb
    biimpar
end
