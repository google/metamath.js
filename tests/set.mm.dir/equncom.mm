include "cun.mm"
include "uncom.mm"
include "eqeq2i.mm"

theorem equncom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = ( B u. C ) <-> A = ( C u. B ) )

  proof
    cB
    cC
    cun
    cC
    cB
    cun
    cA
    cB
    cC
    uncom
    eqeq2i
end
