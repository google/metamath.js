include "cxp.mm"
include "wfn.mm"
include "cbs.mm"
include "cfv.mm"
include "xpsdsfn.mm"
include "xpsbas.mm"
include "sqxpeqd.mm"
include "fneq2d.mm"
include "mpbid.mm"

theorem xpsdsfn2
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cM: class M
  let cN: class N
  let cB: class B
  let cC: class C
  let cD: class D
  assume xpsds.t: |- T = ( R Xs. S )
  assume xpsds.x: |- X = ( Base ` R )
  assume xpsds.y: |- Y = ( Base ` S )
  assume xpsds.1: |- ( ph -> R e. V )
  assume xpsds.2: |- ( ph -> S e. W )
  assume xpsds.p: |- P = ( dist ` T )


  assert |- ( ph -> P Fn ( ( Base ` T ) X. ( Base ` T ) ) )

  proof
    wph
    cP
    cX
    cY
    cxp
    #
    @0
    cxp
    #
    wfn
    cP
    cT
    cbs
    cfv
    #
    @2
    cxp
    #
    wfn
    wph
    cP
    cR
    cS
    cT
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    xpsds.p
    xpsdsfn
    wph
    @1
    @3
    cP
    wph
    @0
    @2
    wph
    cR
    cS
    cT
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    xpsbas
    sqxpeqd
    fneq2d
    mpbid
end
