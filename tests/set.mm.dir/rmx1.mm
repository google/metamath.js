include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "crmx.mm"
include "co.mm"
include "wceq.mm"
include "crmy.mm"
include "rmxy1.mm"
include "simpld.mm"

theorem rmx1
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( A rmX 1 ) = A )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    cA
    c1
    crmx
    co
    cA
    wceq
    cA
    c1
    crmy
    co
    c1
    wceq
    cA
    rmxy1
    simpld
end
