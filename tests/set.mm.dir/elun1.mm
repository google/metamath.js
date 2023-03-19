include "cun.mm"
include "ssun1.mm"
include "sseli.mm"

theorem elun1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. B -> A e. ( B u. C ) )

  proof
    cB
    cB
    cC
    cun
    cA
    cB
    cC
    ssun1
    sseli
end
