include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "cmpt.mm"
include "ctopn.mm"
include "csg.mm"
include "cmpt2.mm"
include "eqid.mm"
include "qustgplem.mm"

theorem qustgp
  let cG: class G
  let cH: class H
  let cY: class Y
  let vb: setvar b
  let vt: setvar t
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cF: class F
  let cS: class S
  let cX: class X
  let cK: class K
  let c.mi: class .-
  assume qustgp.h: |- H = ( G /s ( G ~QG Y ) )


  assert |- ( ( G e. TopGrp /\ Y e. ( NrmSGrp ` G ) ) -> H e. TopGrp )

  proof
    vx
    vz
    vw
    vx
    cG
    cbs
    cfv
    #
    vx
    cv
    cG
    cY
    cqg
    co
    #
    cec
    cmpt
    #
    cG
    cH
    cG
    ctopn
    cfv
    #
    cH
    ctopn
    cfv
    #
    vz
    vw
    @0
    @0
    vz
    cv
    vw
    cv
    cG
    csg
    cfv
    co
    @1
    cec
    cmpt2
    #
    @0
    cY
    qustgp.h
    @0
    eqid
    @3
    eqid
    @4
    eqid
    @2
    eqid
    @5
    eqid
    qustgplem
end
