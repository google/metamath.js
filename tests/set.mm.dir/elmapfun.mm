include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wfun.mm"
include "elmapi.mm"
include "ffun.mm"
include "syl.mm"

theorem elmapfun
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B ^m C ) -> Fun A )

  proof
    cA
    cB
    cC
    cmap
    co
    wcel
    cC
    cB
    cA
    wf
    cA
    wfun
    cA
    cB
    cC
    elmapi
    cC
    cB
    cA
    ffun
    syl
end
