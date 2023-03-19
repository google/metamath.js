include "crg.mm"
include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "dvdsr.mm"
include "simplll.mm"
include "simplr.mm"
include "simpllr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "dvdsrmul.mm"
include "sylancom.mm"
include "simpr.mm"
include "ringass.mm"
include "syl13anc.mm"
include "breqtrrd.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem dvdsrmul1
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vz: setvar z
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )
  assume dvdsrmul1.3: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ Z e. B /\ X .|| Y ) -> ( X .x. Z ) .|| ( Y .x. Z ) )

  proof
    cR
    crg
    wcel
    #
    cZ
    cB
    wcel
    #
    cX
    cY
    c.pa
    wbr
    #
    cX
    cZ
    c.x
    co
    #
    cY
    cZ
    c.x
    co
    #
    c.pa
    wbr
    #
    @2
    cX
    cB
    wcel
    #
    vx
    cv
    #
    cX
    c.x
    co
    #
    cY
    wceq
    #
    vx
    cB
    wrex
    #
    wa
    @0
    @1
    wa
    #
    @5
    vx
    cB
    c.pa
    cR
    c.x
    cX
    cY
    dvdsr.1
    dvdsr.2
    dvdsrmul1.3
    dvdsr
    @11
    @6
    @10
    @5
    @11
    @6
    wa
    #
    @9
    @5
    vx
    cB
    @12
    @7
    cB
    wcel
    #
    wa
    #
    @3
    @8
    cZ
    c.x
    co
    #
    c.pa
    wbr
    @9
    @5
    @14
    @3
    @7
    @3
    c.x
    co
    #
    @15
    c.pa
    @12
    @13
    @3
    cB
    wcel
    #
    @3
    @16
    c.pa
    wbr
    @14
    @0
    @6
    @1
    @17
    @0
    @1
    @6
    @13
    simplll
    #
    @11
    @6
    @13
    simplr
    #
    @0
    @1
    @6
    @13
    simpllr
    #
    cB
    cR
    c.x
    cX
    cZ
    dvdsr.1
    dvdsrmul1.3
    ringcl
    syl3anc
    cB
    c.pa
    cR
    c.x
    @3
    @7
    dvdsr.1
    dvdsr.2
    dvdsrmul1.3
    dvdsrmul
    sylancom
    @14
    @0
    @13
    @6
    @1
    @15
    @16
    wceq
    @18
    @12
    @13
    simpr
    @19
    @20
    cB
    cR
    c.x
    @7
    cX
    cZ
    dvdsr.1
    dvdsrmul1.3
    ringass
    syl13anc
    breqtrrd
    @9
    @15
    @4
    @3
    c.pa
    @8
    cY
    cZ
    c.x
    oveq1
    breq2d
    syl5ibcom
    rexlimdva
    expimpd
    syl5bi
    3impia
end
