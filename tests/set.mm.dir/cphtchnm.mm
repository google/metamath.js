include "ccph.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cnm.mm"
include "eqid.mm"
include "cphnmfval.mm"
include "clmod.mm"
include "cgrp.mm"
include "wceq.mm"
include "cphlmod.mm"
include "lmodgrp.mm"
include "tchnmfval.mm"
include "3syl.mm"
include "eqtr4d.mm"

theorem cphtchnm
  let cG: class G
  let cN: class N
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
  assume cphtchnm.n: |- N = ( norm ` W )


  assert |- ( W e. CPreHil -> N = ( norm ` G ) )

  proof
    cW
    ccph
    wcel
    #
    cN
    vx
    cW
    cbs
    cfv
    #
    vx
    cv
    #
    @2
    cW
    cip
    cfv
    #
    co
    csqrt
    cfv
    cmpt
    #
    cG
    cnm
    cfv
    #
    vx
    @3
    cN
    @1
    cW
    @1
    eqid
    #
    @3
    eqid
    #
    cphtchnm.n
    cphnmfval
    @0
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    @5
    @4
    wceq
    cW
    cphlmod
    cW
    lmodgrp
    vx
    cG
    @3
    @5
    @1
    cW
    tchval.n
    @5
    eqid
    @6
    @7
    tchnmfval
    3syl
    eqtr4d
end
