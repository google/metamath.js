include "cmnd.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cof.mm"
include "wf.mm"
include "cvv.mm"
include "cv.mm"
include "wa.mm"
include "mndcl.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "elmapi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "elmapex.mm"
include "simprd.mm"
include "inidm.mm"
include "off.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem mndvcl
  let cB: class B
  let c.pl: class .+
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mndvcl.b: |- B = ( Base ` M )
  assume mndvcl.p: |- .+ = ( +g ` M )


  assert |- ( ( M e. Mnd /\ X e. ( B ^m I ) /\ Y e. ( B ^m I ) ) -> ( X oF .+ Y ) e. ( B ^m I ) )

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
    w3a
    #
    cX
    cY
    c.pl
    cof
    co
    #
    @1
    wcel
    #
    cI
    cB
    @5
    wf
    #
    @4
    vx
    vy
    cI
    cI
    cI
    c.pl
    cB
    cB
    cB
    cX
    cY
    cvv
    cvv
    @0
    @2
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    @8
    @10
    c.pl
    co
    cB
    wcel
    #
    @3
    @0
    @9
    @11
    @12
    cB
    c.pl
    cM
    @8
    @10
    mndvcl.b
    mndvcl.p
    mndcl
    3expb
    3ad2antl1
    @2
    @0
    cI
    cB
    cX
    wf
    @3
    cX
    cB
    cI
    elmapi
    3ad2ant2
    @3
    @0
    cI
    cB
    cY
    wf
    @2
    cY
    cB
    cI
    elmapi
    3ad2ant3
    @2
    @0
    cI
    cvv
    wcel
    #
    @3
    @2
    cB
    cvv
    wcel
    #
    @13
    cX
    cB
    cI
    elmapex
    simprd
    3ad2ant2
    #
    @15
    cI
    inidm
    off
    @4
    @14
    @13
    @6
    @7
    wb
    cB
    cM
    cbs
    cfv
    cvv
    mndvcl.b
    cM
    cbs
    fvex
    eqeltri
    @15
    cB
    cI
    @5
    cvv
    cvv
    elmapg
    sylancr
    mpbird
end
