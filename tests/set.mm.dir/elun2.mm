include "cun.mm"
include "ssun2.mm"
include "sseli.mm"

theorem elun2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. B -> A e. ( C u. B ) )

  proof
    cB
    cC
    cB
    cun
    cA
    cB
    cC
    ssun2
    sseli
end
