include "cdrs.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cpreset.mm"
include "c0.mm"
include "wne.mm"
include "isdrs.mm"
include "simp3bi.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem drsdir
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vb: setvar b
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume isdrs.b: |- B = ( Base ` K )
  assume isdrs.l: |- .<_ = ( le ` K )

  disjoint K z
  disjoint B z
  disjoint .<_ z
  disjoint X z
  disjoint Y z
  disjoint K f
  disjoint K b
  disjoint K r
  disjoint K x
  disjoint K y
  disjoint b f
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B f
  disjoint B b
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint .<_ f
  disjoint .<_ b
  disjoint .<_ r
  disjoint .<_ x
  disjoint .<_ y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( K e. Dirset /\ X e. B /\ Y e. B ) -> E. z e. B ( X .<_ z /\ Y .<_ z ) )

  proof
    cK
    cdrs
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    vz
    cv
    #
    c.le
    wbr
    #
    cY
    @3
    c.le
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    #
    @0
    vx
    cv
    #
    @3
    c.le
    wbr
    #
    vy
    cv
    #
    @3
    c.le
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @2
    wa
    @7
    @0
    cK
    cpreset
    wcel
    cB
    c0
    wne
    @14
    vx
    vy
    vz
    cB
    cK
    c.le
    isdrs.b
    isdrs.l
    isdrs
    simp3bi
    @13
    @7
    @4
    @11
    wa
    #
    vz
    cB
    wrex
    vx
    vy
    cX
    cY
    cB
    cB
    @8
    cX
    wceq
    #
    @12
    @15
    vz
    cB
    @16
    @9
    @4
    @11
    @8
    cX
    @3
    c.le
    breq1
    anbi1d
    rexbidv
    @10
    cY
    wceq
    #
    @15
    @6
    vz
    cB
    @17
    @11
    @5
    @4
    @10
    cY
    @3
    c.le
    breq1
    anbi2d
    rexbidv
    rspc2v
    syl5com
    3impib
end
