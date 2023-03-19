include "wss.mm"
include "cun.mm"
include "unss1.mm"
include "uncom.mm"
include "3sstr4g.mm"

theorem unss2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( C u. A ) C_ ( C u. B ) )

  proof
    cA
    cB
    wss
    cA
    cC
    cun
    cB
    cC
    cun
    cC
    cA
    cun
    cC
    cB
    cun
    cA
    cB
    cC
    unss1
    cC
    cA
    uncom
    cC
    cB
    uncom
    3sstr4g
end
