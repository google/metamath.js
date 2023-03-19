include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "elpaddn0.mm"
include "syl31anc.mm"
include "wi.mm"
include "simpr.mm"
include "paddasslem15.mm"
include "syl3anl3.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdvv.mm"
include "expimpd.mm"
include "sylbid.mm"
include "ssrdv.mm"

theorem paddasslem16
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vp: setvar p
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( ( X =/= (/) /\ ( Y .+ Z ) =/= (/) ) /\ ( Y =/= (/) /\ Z =/= (/) ) ) ) -> ( X .+ ( Y .+ Z ) ) C_ ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    cZ
    cA
    wss
    #
    w3a
    #
    cX
    c0
    wne
    cY
    cZ
    c.pl
    co
    #
    c0
    wne
    wa
    #
    cY
    c0
    wne
    cZ
    c0
    wne
    wa
    #
    wa
    #
    w3a
    #
    vp
    cX
    @5
    c.pl
    co
    #
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    #
    @9
    vp
    cv
    #
    @10
    wcel
    #
    @12
    cA
    wcel
    #
    @12
    vx
    cv
    #
    vr
    cv
    #
    c.or
    co
    c.le
    wbr
    #
    vr
    @5
    wrex
    vx
    cX
    wrex
    #
    wa
    #
    @12
    @11
    wcel
    #
    @9
    cK
    clat
    wcel
    #
    @1
    @5
    cA
    wss
    #
    @6
    @13
    @19
    wb
    @0
    @4
    @21
    @8
    cK
    hllat
    3ad2ant1
    @0
    @1
    @2
    @3
    @8
    simp21
    @9
    @0
    @2
    @3
    @22
    @0
    @4
    @8
    simp1
    @0
    @1
    @2
    @3
    @8
    simp22
    @0
    @1
    @2
    @3
    @8
    simp23
    cA
    chlt
    c.pl
    cK
    cY
    cZ
    paddasslem.a
    paddasslem.p
    paddssat
    syl3anc
    @0
    @4
    @6
    @7
    simp3l
    cA
    c.pl
    @12
    c.or
    cK
    c.le
    cX
    @5
    vr
    vx
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    elpaddn0
    syl31anc
    @9
    @14
    @18
    @20
    @9
    @14
    wa
    @17
    @20
    vx
    vr
    cX
    @5
    @9
    @14
    @15
    cX
    wcel
    @16
    @5
    wcel
    wa
    #
    @17
    @20
    wi
    wi
    @9
    @14
    @23
    @17
    @20
    @8
    @0
    @4
    @7
    @14
    @23
    @17
    w3a
    @20
    @6
    @7
    simpr
    vx
    cA
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem15
    syl3anl3
    3exp2
    imp
    rexlimdvv
    expimpd
    sylbid
    ssrdv
end
