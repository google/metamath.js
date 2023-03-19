include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "crmx.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "crmy.mm"
include "rmxy0.mm"
include "simpld.mm"

theorem rmx0
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 0 ) = 1 )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    cA
    cc0
    crmx
    co
    c1
    wceq
    cA
    cc0
    crmy
    co
    cc0
    wceq
    cA
    rmxy0
    simpld
end
