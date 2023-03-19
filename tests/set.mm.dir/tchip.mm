include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cip.mm"
include "wceq.mm"
include "eqid.mm"
include "tchex.mm"
include "tchval.mm"
include "tngip.mm"
include "ax-mp.mm"

theorem tchip
  let c.x: class .x.
  let cG: class G
  let cW: class W
  let c.mi: class .-
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.xi: class .,
  let cF: class F
  let cV: class V
  let cC: class C
  let wph: wff ph
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchip.s: |- .x. = ( .i ` W )


  assert |- .x. = ( .i ` G )

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
    c.x
    co
    csqrt
    cfv
    cmpt
    #
    cvv
    wcel
    c.x
    cG
    cip
    cfv
    wceq
    vx
    c.x
    @0
    cW
    @0
    eqid
    #
    tchex
    cG
    cW
    c.x
    @2
    cvv
    vx
    cG
    c.x
    @0
    cW
    tchval.n
    @3
    tchip.s
    tchval
    tchip.s
    tngip
    ax-mp
end
