include "cdm.mm"
include "cxp.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cop.mm"
include "caov.mm"
include "cvv.mm"
include "opelxp.mm"
include "wb.mm"
include "eleq2.mm"
include "eqcoms.mm"
include "syl5bbr.mm"
include "notbid.mm"
include "biimpa.mm"
include "ndmaov.mm"
include "syl.mm"

theorem ndmaovg
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( dom F = ( R X. S ) /\ -. ( A e. R /\ B e. S ) ) -> (( A F B )) = _V )

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
    cop
    #
    @0
    wcel
    #
    wn
    #
    cA
    cB
    cF
    caov
    cvv
    wceq
    @2
    @4
    @7
    @2
    @3
    @6
    @3
    @5
    @1
    wcel
    #
    @2
    @6
    cA
    cB
    cR
    cS
    opelxp
    @8
    @6
    wb
    @1
    @0
    @1
    @0
    @5
    eleq2
    eqcoms
    syl5bbr
    notbid
    biimpa
    cA
    cB
    cF
    ndmaov
    syl
end
