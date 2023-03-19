include "cgrp.mm"
include "wcel.mm"
include "ccom.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cds.mm"
include "eqid.mm"
include "tchnmfval.mm"
include "coeq1d.mm"
include "cvv.mm"
include "wceq.mm"
include "tchex.mm"
include "tchval.mm"
include "tngds.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem tchds
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cW: class W
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
  assume tchds.n: |- N = ( norm ` G )
  assume tchds.m: |- .- = ( -g ` W )


  assert |- ( W e. Grp -> ( N o. .- ) = ( dist ` G ) )

  proof
    cW
    cgrp
    wcel
    #
    cN
    c.mi
    ccom
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
    c.mi
    ccom
    #
    cG
    cds
    cfv
    #
    @0
    cN
    @4
    c.mi
    vx
    cG
    @3
    cN
    @1
    cW
    tchval.n
    tchds.n
    @1
    eqid
    #
    @3
    eqid
    #
    tchnmfval
    coeq1d
    @4
    cvv
    wcel
    @5
    @6
    wceq
    vx
    @3
    @1
    cW
    @7
    tchex
    cG
    cW
    c.mi
    @4
    cvv
    vx
    cG
    @3
    @1
    cW
    tchval.n
    @7
    @8
    tchval
    tchds.m
    tngds
    ax-mp
    syl6eq
end
