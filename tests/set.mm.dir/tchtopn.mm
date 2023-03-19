include "wcel.mm"
include "cmopn.mm"
include "cfv.mm"
include "ctopn.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "eqid.mm"
include "tchex.mm"
include "tchval.mm"
include "tngtopn.mm"
include "mpan2.mm"
include "syl6reqr.mm"

theorem tchtopn
  let cD: class D
  let cG: class G
  let cJ: class J
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
  assume tchtopn.d: |- D = ( dist ` G )
  assume tchtopn.j: |- J = ( TopOpen ` G )


  assert |- ( W e. V -> J = ( MetOpen ` D ) )

  proof
    cW
    cV
    wcel
    #
    cD
    cmopn
    cfv
    #
    cG
    ctopn
    cfv
    #
    cJ
    @0
    vx
    cW
    cbs
    cfv
    #
    vx
    cv
    #
    @4
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
    @1
    @2
    wceq
    vx
    @5
    @3
    cW
    @3
    eqid
    #
    tchex
    cD
    cG
    cW
    @1
    @6
    cV
    cvv
    vx
    cG
    @5
    @3
    cW
    tchval.n
    @7
    @5
    eqid
    tchval
    tchtopn.d
    @1
    eqid
    tngtopn
    mpan2
    tchtopn.j
    syl6reqr
end
