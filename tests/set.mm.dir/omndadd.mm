include "comnd.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cmnd.mm"
include "ctos.mm"
include "isomnd.mm"
include "simp3bi.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq1.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "rspc3v.mm"
include "mpan9.mm"
include "3impia.mm"

theorem omndadd
  let cB: class B
  let c.pl: class .+
  let c.le: class .<_
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume omndadd.0: |- B = ( Base ` M )
  assume omndadd.1: |- .<_ = ( le ` M )
  assume omndadd.2: |- .+ = ( +g ` M )


  assert |- ( ( M e. oMnd /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X .<_ Y ) -> ( X .+ Z ) .<_ ( Y .+ Z ) )

  proof
    cM
    comnd
    wcel
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
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cZ
    c.pl
    co
    #
    cY
    cZ
    c.pl
    co
    #
    c.le
    wbr
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    c.le
    wbr
    #
    @6
    vc
    cv
    #
    c.pl
    co
    #
    @7
    @9
    c.pl
    co
    #
    c.le
    wbr
    #
    wi
    #
    vc
    cB
    wral
    vb
    cB
    wral
    va
    cB
    wral
    #
    @1
    @2
    @5
    wi
    #
    @0
    cM
    cmnd
    wcel
    cM
    ctos
    wcel
    @14
    cB
    c.pl
    c.le
    cM
    va
    vb
    vc
    omndadd.0
    omndadd.2
    omndadd.1
    isomnd
    simp3bi
    @13
    @15
    cX
    @7
    c.le
    wbr
    #
    cX
    @9
    c.pl
    co
    #
    @11
    c.le
    wbr
    #
    wi
    @2
    @17
    cY
    @9
    c.pl
    co
    #
    c.le
    wbr
    #
    wi
    va
    vb
    vc
    cX
    cY
    cZ
    cB
    cB
    cB
    @6
    cX
    wceq
    #
    @8
    @16
    @12
    @18
    @6
    cX
    @7
    c.le
    breq1
    @21
    @10
    @17
    @11
    c.le
    @6
    cX
    @9
    c.pl
    oveq1
    breq1d
    imbi12d
    @7
    cY
    wceq
    #
    @16
    @2
    @18
    @20
    @7
    cY
    cX
    c.le
    breq2
    @22
    @11
    @19
    @17
    c.le
    @7
    cY
    @9
    c.pl
    oveq1
    breq2d
    imbi12d
    @9
    cZ
    wceq
    #
    @20
    @5
    @2
    @23
    @17
    @3
    @19
    @4
    c.le
    @9
    cZ
    cX
    c.pl
    oveq2
    @9
    cZ
    cY
    c.pl
    oveq2
    breq12d
    imbi2d
    rspc3v
    mpan9
    3impia
end
