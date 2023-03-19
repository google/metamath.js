include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "fimax2g.mm"
include "wb.mm"
include "wa.mm"
include "weq.mm"
include "wo.mm"
include "df-ne.mm"
include "imbi1i.mm"
include "pm4.64.mm"
include "bitri.mm"
include "sotric.mm"
include "con2bid.mm"
include "syl5bb.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem fimaxg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( R Or A /\ A e. Fin /\ A =/= (/) ) -> E. x e. A A. y e. A ( x =/= y -> y R x ) )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @4
    @3
    cR
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @3
    @4
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    vx
    vy
    cA
    cR
    fimax2g
    @0
    @1
    @9
    @13
    wb
    @2
    @0
    @8
    @12
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    wa
    @7
    @11
    vy
    cA
    @0
    @14
    @4
    cA
    wcel
    #
    @7
    @11
    wb
    @7
    vx
    vy
    weq
    #
    @6
    wo
    #
    @0
    @14
    @15
    wa
    wa
    #
    @11
    @7
    @16
    wn
    #
    @6
    wi
    @17
    @5
    @19
    @6
    @3
    @4
    df-ne
    imbi1i
    @16
    @6
    pm4.64
    bitri
    @18
    @10
    @17
    cA
    @3
    @4
    cR
    sotric
    con2bid
    syl5bb
    anassrs
    ralbidva
    rexbidva
    3ad2ant1
    mpbird
end
