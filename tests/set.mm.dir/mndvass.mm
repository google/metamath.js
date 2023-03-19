include "cmnd.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "cvv.mm"
include "elmapex.mm"
include "simprd.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "wf.mm"
include "elmapi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "cv.mm"
include "wceq.mm"
include "mndass.mm"
include "adantlr.mm"
include "caofass.mm"

theorem mndvass
  let cB: class B
  let c.pl: class .+
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  assume mndvcl.b: |- B = ( Base ` M )
  assume mndvcl.p: |- .+ = ( +g ` M )


  assert |- ( ( M e. Mnd /\ ( X e. ( B ^m I ) /\ Y e. ( B ^m I ) /\ Z e. ( B ^m I ) ) ) -> ( ( X oF .+ Y ) oF .+ Z ) = ( X oF .+ ( Y oF .+ Z ) ) )

  proof
    cM
    cmnd
    wcel
    #
    cX
    cB
    cI
    cmap
    co
    #
    wcel
    #
    cY
    @1
    wcel
    #
    cZ
    @1
    wcel
    #
    w3a
    #
    wa
    vx
    vy
    vz
    cI
    c.pl
    c.pl
    cB
    c.pl
    cX
    cY
    cZ
    c.pl
    cvv
    @5
    cI
    cvv
    wcel
    #
    @0
    @2
    @3
    @6
    @4
    @2
    cB
    cvv
    wcel
    @6
    cX
    cB
    cI
    elmapex
    simprd
    3ad2ant1
    adantl
    @5
    cI
    cB
    cX
    wf
    #
    @0
    @2
    @3
    @7
    @4
    cX
    cB
    cI
    elmapi
    3ad2ant1
    adantl
    @5
    cI
    cB
    cY
    wf
    #
    @0
    @3
    @2
    @8
    @4
    cY
    cB
    cI
    elmapi
    3ad2ant2
    adantl
    @5
    cI
    cB
    cZ
    wf
    #
    @0
    @4
    @2
    @9
    @3
    cZ
    cB
    cI
    elmapi
    3ad2ant3
    adantl
    @0
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    vz
    cv
    #
    cB
    wcel
    w3a
    @10
    @11
    c.pl
    co
    @12
    c.pl
    co
    @10
    @11
    @12
    c.pl
    co
    c.pl
    co
    wceq
    @5
    cB
    c.pl
    cM
    @10
    @11
    @12
    mndvcl.b
    mndvcl.p
    mndass
    adantlr
    caofass
end
