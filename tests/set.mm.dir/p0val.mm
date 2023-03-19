include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cp0.mm"
include "cv.mm"
include "cbs.mm"
include "cglb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq12d.mm"
include "df-p0.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem p0val
  let cB: class B
  let cG: class G
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let vp: setvar p
  assume p0val.b: |- B = ( Base ` K )
  assume p0val.g: |- G = ( glb ` K )
  assume p0val.z: |- .0. = ( 0. ` K )


  assert |- ( K e. V -> .0. = ( G ` B ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    #
    c.0
    cB
    cG
    cfv
    #
    wceq
    cK
    cV
    elex
    @0
    c.0
    cK
    cp0
    cfv
    @1
    p0val.z
    vp
    cK
    vp
    cv
    #
    cbs
    cfv
    #
    @2
    cglb
    cfv
    #
    cfv
    @1
    cvv
    cp0
    @2
    cK
    wceq
    #
    @3
    cB
    @4
    cG
    @5
    @4
    cK
    cglb
    cfv
    cG
    @2
    cK
    cglb
    fveq2
    p0val.g
    syl6eqr
    @5
    @3
    cK
    cbs
    cfv
    cB
    @2
    cK
    cbs
    fveq2
    p0val.b
    syl6eqr
    fveq12d
    vp
    df-p0
    cB
    cG
    fvex
    fvmpt
    syl5eq
    syl
end
