include "cdm.mm"
include "cxp.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "c0.mm"
include "df-ov.mm"
include "eleq2.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "notbid.mm"
include "ndmfv.mm"
include "syl6bir.mm"
include "imp.mm"
include "syl5eq.mm"

theorem ndmovg
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( ( dom F = ( R X. S ) /\ -. ( A e. R /\ B e. S ) ) -> ( A F B ) = (/) )

  proof
    cF
    cdm
    #
    cR
    cS
    cxp
    #
    wceq
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
    #
    wa
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
    @2
    @4
    @6
    c0
    wceq
    #
    @2
    @4
    @5
    @0
    wcel
    #
    wn
    @7
    @2
    @8
    @3
    @2
    @8
    @5
    @1
    wcel
    @3
    @0
    @1
    @5
    eleq2
    cA
    cB
    cR
    cS
    opelxp
    syl6bb
    notbid
    @5
    cF
    ndmfv
    syl6bir
    imp
    syl5eq
end
