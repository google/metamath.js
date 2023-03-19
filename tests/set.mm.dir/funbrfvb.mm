include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "funfn.mm"
include "fnbrfvb.mm"
include "sylanb.mm"

theorem funbrfvb
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A e. dom F ) -> ( ( F ` A ) = B <-> A F B ) )

  proof
    cF
    wfun
    cF
    cF
    cdm
    #
    wfn
    cA
    @0
    wcel
    cA
    cF
    cfv
    cB
    wceq
    cA
    cB
    cF
    wbr
    wb
    cF
    funfn
    @0
    cA
    cB
    cF
    fnbrfvb
    sylanb
end
