include "wor.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "simp3.mm"
include "simp2.mm"
include "jca.mm"
include "sotric.mm"
include "sylan2.mm"
include "con2bid.mm"
include "adantr.mm"
include "wi.mm"
include "breq2.mm"
include "biimprcd.mm"
include "adantl.mm"
include "sotr.mm"
include "expdimp.mm"
include "jaod.mm"
include "sylbird.mm"
include "expimpd.mm"

theorem sotr3
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( R Or A /\ ( X e. A /\ Y e. A /\ Z e. A ) ) -> ( ( X R Y /\ -. Z R Y ) -> X R Z ) )

  proof
    cA
    cR
    wor
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    cZ
    cA
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cY
    cR
    wbr
    #
    cZ
    cY
    cR
    wbr
    #
    wn
    #
    cX
    cZ
    cR
    wbr
    #
    @5
    @6
    wa
    #
    @8
    cZ
    cY
    wceq
    #
    cY
    cZ
    cR
    wbr
    #
    wo
    #
    @9
    @5
    @13
    @8
    wb
    @6
    @5
    @7
    @13
    @4
    @0
    @3
    @2
    wa
    @7
    @13
    wn
    wb
    @4
    @3
    @2
    @1
    @2
    @3
    simp3
    @1
    @2
    @3
    simp2
    jca
    cA
    cZ
    cY
    cR
    sotric
    sylan2
    con2bid
    adantr
    @10
    @11
    @9
    @12
    @6
    @11
    @9
    wi
    @5
    @11
    @9
    @6
    cZ
    cY
    cX
    cR
    breq2
    biimprcd
    adantl
    @5
    @6
    @12
    @9
    cA
    cX
    cY
    cZ
    cR
    sotr
    expdimp
    jaod
    sylbird
    expimpd
end
