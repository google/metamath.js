include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "mthmblem.mm"
include "wi.mm"
include "eqcoms.mm"
include "impbid.mm"

theorem mthmb
  let cR: class R
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume mthmb.r: |- R = ( mStRed ` T )
  assume mthmb.u: |- U = ( mThm ` T )


  assert |- ( ( R ` X ) = ( R ` Y ) -> ( X e. U <-> Y e. U ) )

  proof
    cX
    cR
    cfv
    #
    cY
    cR
    cfv
    #
    wceq
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    cR
    cT
    cU
    cX
    cY
    mthmb.r
    mthmb.u
    mthmblem
    @3
    @2
    wi
    @1
    @0
    cR
    cT
    cU
    cY
    cX
    mthmb.r
    mthmb.u
    mthmblem
    eqcoms
    impbid
end
