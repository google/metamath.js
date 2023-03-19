include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "wceq.mm"
include "eqid.mm"
include "tchex.mm"
include "tchval.mm"
include "tngplusg.mm"
include "ax-mp.mm"

theorem tchplusg
  let c.pl: class .+
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
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchplusg.v: |- .+ = ( +g ` W )


  assert |- .+ = ( +g ` G )

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
    c.pl
    cG
    cplusg
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
    c.pl
    cG
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
    tchplusg.v
    tngplusg
    ax-mp
end
