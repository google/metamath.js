include "ctos.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "cpo.mm"
include "istos.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "breq1.mm"
include "breq2.mm"
include "orbi12d.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem tleile
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tleile.b: |- B = ( Base ` K )
  assume tleile.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Toset /\ X e. B /\ Y e. B ) -> ( X .<_ Y \/ Y .<_ X ) )

  proof
    cK
    ctos
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
    w3a
    @1
    @2
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    @4
    @3
    c.le
    wbr
    #
    wo
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wo
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @0
    @1
    @8
    @2
    @0
    cK
    cpo
    wcel
    @8
    vx
    vy
    cB
    cK
    c.le
    tleile.b
    tleile.l
    istos
    simprbi
    3ad2ant1
    @7
    @11
    cX
    @4
    c.le
    wbr
    #
    @4
    cX
    c.le
    wbr
    #
    wo
    vx
    vy
    cX
    cY
    cB
    cB
    @3
    cX
    wceq
    @5
    @12
    @6
    @13
    @3
    cX
    @4
    c.le
    breq1
    @3
    cX
    @4
    c.le
    breq2
    orbi12d
    @4
    cY
    wceq
    @12
    @9
    @13
    @10
    @4
    cY
    cX
    c.le
    breq2
    @4
    cY
    cX
    c.le
    breq1
    orbi12d
    rspc2va
    syl21anc
end
