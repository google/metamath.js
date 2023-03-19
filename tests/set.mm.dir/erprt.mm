include "wer.mm"
include "cv.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cqs.mm"
include "wral.mm"
include "wprt.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "qsdisj.mm"
include "ralrimivva.mm"
include "df-prt.mm"
include "sylibr.mm"

theorem erprt
  let cA: class A
  let c.sm: class .~
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( .~ Er X -> Prt ( A /. .~ ) )

  proof
    cX
    c.sm
    wer
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @1
    @2
    cin
    c0
    wceq
    wo
    #
    vy
    cA
    c.sm
    cqs
    #
    wral
    vx
    @4
    wral
    @4
    wprt
    @0
    @3
    vx
    vy
    @4
    @4
    @0
    @1
    @4
    wcel
    #
    @2
    @4
    wcel
    #
    wa
    #
    wa
    cA
    @1
    @2
    c.sm
    cX
    @0
    @7
    simpl
    @0
    @5
    @6
    simprl
    @0
    @5
    @6
    simprr
    qsdisj
    ralrimivva
    vx
    vy
    @4
    df-prt
    sylibr
end
