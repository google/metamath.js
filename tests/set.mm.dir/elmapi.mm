include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "elmapex.mm"
include "elmapg.mm"
include "syl.mm"
include "ibi.mm"

theorem elmapi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B ^m C ) -> A : C --> B )

  proof
    cA
    cB
    cC
    cmap
    co
    wcel
    #
    cC
    cB
    cA
    wf
    #
    @0
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    wa
    @0
    @1
    wb
    cA
    cB
    cC
    elmapex
    cB
    cC
    cA
    cvv
    cvv
    elmapg
    syl
    ibi
end
