include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "wfn.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "opelxpi.mm"
include "fnbrfvb.mm"
include "sylan2.mm"

theorem fnbrfvb2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( F Fn ( V X. W ) /\ ( A e. V /\ B e. W ) ) -> ( ( F ` <. A , B >. ) = C <-> <. A , B >. F C ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cF
    cV
    cW
    cxp
    #
    wfn
    cA
    cB
    cop
    #
    @0
    wcel
    @1
    cF
    cfv
    cC
    wceq
    @1
    cC
    cF
    wbr
    wb
    cA
    cB
    cV
    cW
    opelxpi
    @0
    @1
    cC
    cF
    fnbrfvb
    sylan2
end
