include "cxp.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cprds.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "cvv.mm"
include "eqid.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wf1o.mm"
include "wfo.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "f1ofo.mm"
include "mp1i.mm"
include "ovexd.mm"
include "imasbas.mm"

theorem xpsbas
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vd: setvar d
  let cC: class C
  let cG: class G
  let cD: class D
  let cF: class F
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let c.x: class .x.
  let c.xp: class .X.
  let c.xb: class .xb
  assume xpsval.t: |- T = ( R Xs. S )
  assume xpsval.x: |- X = ( Base ` R )
  assume xpsval.y: |- Y = ( Base ` S )
  assume xpsval.1: |- ( ph -> R e. V )
  assume xpsval.2: |- ( ph -> S e. W )


  assert |- ( ph -> ( X X. Y ) = ( Base ` T ) )

  proof
    wph
    cX
    cY
    cxp
    #
    cR
    csca
    cfv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cprds
    co
    #
    cT
    vx
    vy
    cX
    cY
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    ccnv
    #
    @4
    crn
    #
    cvv
    wph
    vx
    vy
    cR
    cS
    cT
    @3
    @4
    @1
    cV
    cW
    cX
    cY
    xpsval.t
    xpsval.x
    xpsval.y
    xpsval.1
    xpsval.2
    @4
    eqid
    #
    @1
    eqid
    #
    @3
    eqid
    #
    xpsval
    wph
    vx
    vy
    cR
    cS
    cT
    @3
    @4
    @1
    cV
    cW
    cX
    cY
    xpsval.t
    xpsval.x
    xpsval.y
    xpsval.1
    xpsval.2
    @7
    @8
    @9
    xpslem
    @6
    @0
    @5
    wf1o
    #
    @6
    @0
    @5
    wfo
    wph
    @0
    @6
    @4
    wf1o
    @10
    vx
    vy
    cX
    cY
    @4
    @7
    xpsff1o2
    @0
    @6
    @4
    f1ocnv
    ax-mp
    @6
    @0
    @5
    f1ofo
    mp1i
    wph
    @1
    @2
    cprds
    ovexd
    imasbas
end
