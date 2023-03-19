include "cmnd.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cvv.mm"
include "elmapex.mm"
include "simprd.mm"
include "adantl.mm"
include "wf.mm"
include "elmapi.mm"
include "mndidcl.mm"
include "adantr.mm"
include "cv.mm"
include "wceq.mm"
include "mndlid.mm"
include "adantlr.mm"
include "caofid0l.mm"

theorem mndvlid
  let cB: class B
  let c.pl: class .+
  let cI: class I
  let cM: class M
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let vz: setvar z
  let cZ: class Z
  assume mndvcl.b: |- B = ( Base ` M )
  assume mndvcl.p: |- .+ = ( +g ` M )
  assume mndvlid.z: |- .0. = ( 0g ` M )


  assert |- ( ( M e. Mnd /\ X e. ( B ^m I ) ) -> ( ( I X. { .0. } ) oF .+ X ) = X )

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
    wcel
    #
    wa
    vx
    cI
    c.0
    c.pl
    cB
    cX
    cvv
    cB
    @1
    cI
    cvv
    wcel
    #
    @0
    @1
    cB
    cvv
    wcel
    @2
    cX
    cB
    cI
    elmapex
    simprd
    adantl
    @1
    cI
    cB
    cX
    wf
    @0
    cX
    cB
    cI
    elmapi
    adantl
    @0
    c.0
    cB
    wcel
    @1
    cB
    cM
    c.0
    mndvcl.b
    mndvlid.z
    mndidcl
    adantr
    @0
    vx
    cv
    #
    cB
    wcel
    c.0
    @3
    c.pl
    co
    @3
    wceq
    @1
    cB
    c.pl
    cM
    @3
    c.0
    mndvcl.b
    mndvcl.p
    mndvlid.z
    mndlid
    adantlr
    caofid0l
end
