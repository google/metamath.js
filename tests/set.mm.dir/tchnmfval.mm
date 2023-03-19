include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmpt.mm"
include "cnm.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "fvrn0.mm"
include "a1i.mm"
include "fmpti.mm"
include "tchval.mm"
include "cc.mm"
include "cnex.mm"
include "wss.mm"
include "sqrtf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "p0ex.mm"
include "unex.mm"
include "tngnm.mm"
include "mpan2.mm"
include "syl6reqr.mm"

theorem tchnmfval
  let vx: setvar x
  let cG: class G
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let c.mi: class .-
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cC: class C
  let wph: wff ph
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchnmval.n: |- N = ( norm ` G )
  assume tchnmval.v: |- V = ( Base ` W )
  assume tchnmval.h: |- ., = ( .i ` W )

  disjoint ., x
  disjoint G x
  disjoint V x
  disjoint W x
  disjoint .- x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ., w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ., y
  disjoint ., z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint W w
  disjoint W y
  disjoint W z
  disjoint .x. x
  disjoint X x
  disjoint Y x
  assert |- ( W e. Grp -> N = ( x e. V |-> ( sqrt ` ( x ., x ) ) ) )

  proof
    cW
    cgrp
    wcel
    #
    vx
    cV
    vx
    cv
    #
    @1
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    cG
    cnm
    cfv
    #
    cN
    @0
    cV
    csqrt
    crn
    #
    c0
    csn
    #
    cun
    #
    @4
    wf
    @4
    @5
    wceq
    vx
    cV
    @8
    @3
    @4
    @4
    eqid
    @3
    @8
    wcel
    @1
    cV
    wcel
    csqrt
    @2
    fvrn0
    a1i
    fmpti
    @8
    cG
    cW
    @4
    cV
    vx
    cG
    c.xi
    cV
    cW
    tchval.n
    tchnmval.v
    tchnmval.h
    tchval
    tchnmval.v
    @6
    @7
    @6
    cc
    cnex
    cc
    cc
    csqrt
    wf
    @6
    cc
    wss
    sqrtf
    cc
    cc
    csqrt
    frn
    ax-mp
    ssexi
    p0ex
    unex
    tngnm
    mpan2
    tchnmval.n
    syl6reqr
end
