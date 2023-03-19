include "csur.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "nosepon.mm"
include "onelon.mm"
include "sylan.mm"
include "simpr.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "onnminsb.mm"
include "sylc.mm"
include "df-ne.mm"
include "con2bii.mm"
include "sylibr.mm"

theorem nosepeq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X

  disjoint A x
  disjoint B x
  disjoint X x
  assert |- ( ( ( A e. No /\ B e. No /\ A =/= B ) /\ X e. |^| { x e. On | ( A ` x ) =/= ( B ` x ) } ) -> ( A ` X ) = ( B ` X ) )

  proof
    cA
    csur
    wcel
    cB
    csur
    wcel
    cA
    cB
    wne
    w3a
    #
    cX
    vx
    cv
    #
    cA
    cfv
    #
    @1
    cB
    cfv
    #
    wne
    #
    vx
    con0
    crab
    cint
    #
    wcel
    #
    wa
    #
    cX
    cA
    cfv
    #
    cX
    cB
    cfv
    #
    wne
    #
    wn
    #
    @8
    @9
    wceq
    #
    @7
    cX
    con0
    wcel
    #
    @6
    @11
    @0
    @5
    con0
    wcel
    @6
    @13
    vx
    cA
    cB
    nosepon
    @5
    cX
    onelon
    sylan
    @0
    @6
    simpr
    @4
    @10
    vx
    cX
    @1
    cX
    wceq
    @2
    @8
    @3
    @9
    @1
    cX
    cA
    fveq2
    @1
    cX
    cB
    fveq2
    neeq12d
    onnminsb
    sylc
    @10
    @12
    @8
    @9
    df-ne
    con2bii
    sylibr
end
