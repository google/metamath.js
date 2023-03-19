include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wfn.mm"
include "elmapi.mm"
include "ffn.mm"
include "syl.mm"

theorem elmapfn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B ^m C ) -> A Fn C )

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
    cC
    wfn
    cA
    cB
    cC
    elmapi
    cC
    cB
    cA
    ffn
    syl
end
