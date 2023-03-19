include "cdomn.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "an4.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "domneq0.mm"
include "3expb.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6rbbr.mm"
include "biimpd.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "3impib.mm"

theorem domnmuln0
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume domneq0.b: |- B = ( Base ` R )
  assume domneq0.t: |- .x. = ( .r ` R )
  assume domneq0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Domn /\ ( X e. B /\ X =/= .0. ) /\ ( Y e. B /\ Y =/= .0. ) ) -> ( X .x. Y ) =/= .0. )

  proof
    cR
    cdomn
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    wa
    #
    cY
    cB
    wcel
    #
    cY
    c.0
    wne
    #
    wa
    #
    cX
    cY
    c.x
    co
    #
    c.0
    wne
    #
    @3
    @6
    wa
    @1
    @4
    wa
    #
    @2
    @5
    wa
    #
    wa
    @0
    @8
    @1
    @2
    @4
    @5
    an4
    @0
    @9
    @10
    @8
    @0
    @9
    wa
    #
    @10
    @8
    @11
    @8
    cX
    c.0
    wceq
    cY
    c.0
    wceq
    wo
    #
    wn
    @10
    @11
    @12
    @7
    c.0
    @0
    @1
    @4
    @7
    c.0
    wceq
    @12
    wb
    cB
    cR
    c.x
    cX
    cY
    c.0
    domneq0.b
    domneq0.t
    domneq0.z
    domneq0
    3expb
    necon3abid
    cX
    c.0
    cY
    c.0
    neanior
    syl6rbbr
    biimpd
    expimpd
    syl5bi
    3impib
end
