include "cv.mm"
include "cip.mm"
include "cfv.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "tchex.mm"
include "eqid.mm"
include "tchval.mm"
include "tngbas.mm"
include "ax-mp.mm"

theorem tchbas
  let cG: class G
  let cV: class V
  let cW: class W
  let c.mi: class .-
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.xi: class .,
  let cF: class F
  let cC: class C
  let wph: wff ph
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchbas.v: |- V = ( Base ` W )


  assert |- V = ( Base ` G )

  proof
    vx
    cV
    vx
    cv
    #
    @0
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
    cV
    cG
    cbs
    cfv
    wceq
    vx
    @1
    cV
    cW
    tchbas.v
    tchex
    cV
    cG
    cW
    @2
    cvv
    vx
    cG
    @1
    cV
    cW
    tchval.n
    tchbas.v
    @1
    eqid
    tchval
    tchbas.v
    tngbas
    ax-mp
end
