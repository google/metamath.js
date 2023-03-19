include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "ustssxp.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"

theorem ustrel
  let cU: class U
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cW: class W


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> Rel V )

  proof
    cU
    cX
    cust
    cfv
    wcel
    cV
    cU
    wcel
    wa
    #
    cV
    cvv
    cvv
    cxp
    #
    wss
    cV
    wrel
    @0
    cV
    cX
    cX
    cxp
    @1
    cU
    cV
    cX
    ustssxp
    cX
    cX
    xpss
    syl6ss
    cV
    df-rel
    sylibr
end
