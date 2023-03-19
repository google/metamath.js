include "cpreset.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cvv.mm"
include "isprs.mm"
include "simprbi.mm"
include "wceq.mm"
include "wb.mm"
include "breq12.mm"
include "anidms.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem prslem
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vb: setvar b
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isprs.b: |- B = ( Base ` K )
  assume isprs.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Preset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ X /\ ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) )

  proof
    cK
    cpreset
    wcel
    #
    vx
    cv
    #
    @1
    c.le
    wbr
    #
    @1
    vy
    cv
    #
    c.le
    wbr
    #
    @3
    vz
    cv
    #
    c.le
    wbr
    #
    wa
    #
    @1
    @5
    c.le
    wbr
    #
    wi
    #
    wa
    #
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cX
    c.le
    wbr
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cZ
    c.le
    wbr
    #
    wa
    #
    cX
    cZ
    c.le
    wbr
    #
    wi
    #
    wa
    #
    @0
    cK
    cvv
    wcel
    @11
    vx
    vy
    vz
    cB
    cK
    c.le
    isprs.b
    isprs.l
    isprs
    simprbi
    @10
    @18
    @12
    cX
    @3
    c.le
    wbr
    #
    @6
    wa
    #
    cX
    @5
    c.le
    wbr
    #
    wi
    #
    wa
    @12
    @13
    cY
    @5
    c.le
    wbr
    #
    wa
    #
    @21
    wi
    #
    wa
    vx
    vy
    vz
    cX
    cY
    cZ
    cB
    cB
    cB
    @1
    cX
    wceq
    #
    @2
    @12
    @9
    @22
    @26
    @2
    @12
    wb
    @1
    cX
    @1
    cX
    c.le
    breq12
    anidms
    @26
    @7
    @20
    @8
    @21
    @26
    @4
    @19
    @6
    @1
    cX
    @3
    c.le
    breq1
    anbi1d
    @1
    cX
    @5
    c.le
    breq1
    imbi12d
    anbi12d
    @3
    cY
    wceq
    #
    @22
    @25
    @12
    @27
    @20
    @24
    @21
    @27
    @19
    @13
    @6
    @23
    @3
    cY
    cX
    c.le
    breq2
    @3
    cY
    @5
    c.le
    breq1
    anbi12d
    imbi1d
    anbi2d
    @5
    cZ
    wceq
    #
    @25
    @17
    @12
    @28
    @24
    @15
    @21
    @16
    @28
    @23
    @14
    @13
    @5
    cZ
    cY
    c.le
    breq2
    anbi2d
    @5
    cZ
    cX
    c.le
    breq2
    imbi12d
    anbi2d
    rspc3v
    mpan9
end
