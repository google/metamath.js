include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cbs.mm"
include "cfv.mm"
include "pwsbas.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "wb.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "mpan.mm"
include "adantl.mm"
include "bitr3d.mm"

theorem pwselbasb
  let cB: class B
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  assume pwsbas.y: |- Y = ( R ^s I )
  assume pwsbas.f: |- B = ( Base ` R )
  assume pwselbas.v: |- V = ( Base ` Y )


  assert |- ( ( R e. W /\ I e. Z ) -> ( X e. V <-> X : I --> B ) )

  proof
    cR
    cW
    wcel
    #
    cI
    cZ
    wcel
    #
    wa
    #
    cX
    cB
    cI
    cmap
    co
    #
    wcel
    #
    cX
    cV
    wcel
    cI
    cB
    cX
    wf
    #
    @2
    @3
    cV
    cX
    @2
    @3
    cY
    cbs
    cfv
    cV
    cB
    cR
    cI
    cW
    cZ
    cY
    pwsbas.y
    pwsbas.f
    pwsbas
    pwselbas.v
    syl6eqr
    eleq2d
    @1
    @4
    @5
    wb
    #
    @0
    cB
    cvv
    wcel
    @1
    @6
    cB
    cR
    cbs
    cfv
    cvv
    pwsbas.f
    cR
    cbs
    fvex
    eqeltri
    cB
    cI
    cX
    cvv
    cZ
    elmapg
    mpan
    adantl
    bitr3d
end
