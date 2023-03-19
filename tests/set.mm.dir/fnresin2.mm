include "wfn.mm"
include "cin.mm"
include "wss.mm"
include "cres.mm"
include "inss2.mm"
include "fnssres.mm"
include "mpan2.mm"

theorem fnresin2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F Fn A -> ( F |` ( B i^i A ) ) Fn ( B i^i A ) )

  proof
    cF
    cA
    wfn
    cB
    cA
    cin
    #
    cA
    wss
    cF
    @0
    cres
    @0
    wfn
    cB
    cA
    inss2
    cA
    @0
    cF
    fnssres
    mpan2
end
