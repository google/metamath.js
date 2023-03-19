include "cdm.mm"
include "cxp.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "c0.mm"
include "df-ov.mm"
include "wceq.mm"
include "ssel2.mm"
include "opelxp.mm"
include "sylib.mm"
include "stoic1a.mm"
include "ndmfv.mm"
include "syl.mm"
include "syl5eq.mm"

theorem nssdmovg
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( ( dom F C_ ( R X. S ) /\ -. ( A e. R /\ B e. S ) ) -> ( A F B ) = (/) )

  proof
    cF
    cdm
    #
    cR
    cS
    cxp
    #
    wss
    #
    cA
    cR
    wcel
    cB
    cS
    wcel
    wa
    #
    wn
    wa
    #
    cA
    cB
    cF
    co
    cA
    cB
    cop
    #
    cF
    cfv
    #
    c0
    cA
    cB
    cF
    df-ov
    @4
    @5
    @0
    wcel
    #
    wn
    @6
    c0
    wceq
    @2
    @7
    @3
    @2
    @7
    wa
    @5
    @1
    wcel
    @3
    @0
    @1
    @5
    ssel2
    cA
    cB
    cR
    cS
    opelxp
    sylib
    stoic1a
    @5
    cF
    ndmfv
    syl
    syl5eq
end
