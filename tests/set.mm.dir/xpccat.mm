include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "cop.mm"
include "cmpt2.mm"
include "wceq.mm"
include "eqid.mm"
include "xpccatid.mm"
include "simpld.mm"

theorem xpccat
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let cJ: class J
  let cX: class X
  let cR: class R
  let cS: class S
  let cY: class Y
  assume xpccat.t: |- T = ( C Xc. D )
  assume xpccat.c: |- ( ph -> C e. Cat )
  assume xpccat.d: |- ( ph -> D e. Cat )


  assert |- ( ph -> T e. Cat )

  proof
    wph
    cT
    ccat
    wcel
    cT
    ccid
    cfv
    vx
    vy
    cC
    cbs
    cfv
    #
    cD
    cbs
    cfv
    #
    vx
    cv
    cC
    ccid
    cfv
    #
    cfv
    vy
    cv
    cD
    ccid
    cfv
    #
    cfv
    cop
    cmpt2
    wceq
    wph
    vx
    vy
    cC
    cD
    cT
    @2
    @3
    @0
    @1
    xpccat.t
    xpccat.c
    xpccat.d
    @0
    eqid
    @1
    eqid
    @2
    eqid
    @3
    eqid
    xpccatid
    simpld
end
