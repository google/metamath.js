include "wfn.mm"
include "cin.mm"
include "wss.mm"
include "cres.mm"
include "inss1.mm"
include "fnssres.mm"
include "mpan2.mm"

theorem fnresin1
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F Fn A -> ( F |` ( A i^i B ) ) Fn ( A i^i B ) )

  proof
    cF
    cA
    wfn
    cA
    cB
    cin
    #
    cA
    wss
    cF
    @0
    cres
    @0
    wfn
    cA
    cB
    inss1
    cA
    @0
    cF
    fnssres
    mpan2
end
