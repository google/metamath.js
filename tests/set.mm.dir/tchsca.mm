include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "csca.mm"
include "wceq.mm"
include "eqid.mm"
include "tchex.mm"
include "tchval.mm"
include "tngsca.mm"
include "ax-mp.mm"

theorem tchsca
  let cF: class F
  let cG: class G
  let cW: class W
  let c.mi: class .-
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.xi: class .,
  let cV: class V
  let cC: class C
  let wph: wff ph
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchsca.f: |- F = ( Scalar ` W )


  assert |- F = ( Scalar ` G )

  proof
    vx
    cW
    cbs
    cfv
    #
    vx
    cv
    #
    @1
    cW
    cip
    cfv
    #
    co
    csqrt
    cfv
    cmpt
    #
    cvv
    wcel
    cF
    cG
    csca
    cfv
    wceq
    vx
    @2
    @0
    cW
    @0
    eqid
    #
    tchex
    cG
    cF
    cW
    @3
    cvv
    vx
    cG
    @2
    @0
    cW
    tchval.n
    @4
    @2
    eqid
    tchval
    tchsca.f
    tngsca
    ax-mp
end
