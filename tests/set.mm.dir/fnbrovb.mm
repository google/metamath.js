include "co.mm"
include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "df-ov.mm"
include "eqeq1i.mm"
include "fnbrfvb2.mm"
include "syl5bb.mm"

theorem fnbrovb
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( F Fn ( V X. W ) /\ ( A e. V /\ B e. W ) ) -> ( ( A F B ) = C <-> <. A , B >. F C ) )

  proof
    cA
    cB
    cF
    co
    #
    cC
    wceq
    cA
    cB
    cop
    #
    cF
    cfv
    #
    cC
    wceq
    cF
    cV
    cW
    cxp
    wfn
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    wa
    @1
    cC
    cF
    wbr
    @0
    @2
    cC
    cA
    cB
    cF
    df-ov
    eqeq1i
    cA
    cB
    cC
    cF
    cV
    cW
    fnbrfvb2
    syl5bb
end
