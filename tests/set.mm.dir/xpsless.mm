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
include "mp1i.mm"
include "f1ofo.mm"
include "syl.mm"
include "ovexd.mm"
include "imasless.mm"

theorem xpsless
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cD: class D
  assume xpsle.t: |- T = ( R Xs. S )
  assume xpsle.x: |- X = ( Base ` R )
  assume xpsle.y: |- Y = ( Base ` S )
  assume xpsle.1: |- ( ph -> R e. V )
  assume xpsle.2: |- ( ph -> S e. W )
  assume xpsle.p: |- .<_ = ( le ` T )


  assert |- ( ph -> .<_ C_ ( ( X X. Y ) X. ( X X. Y ) ) )

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
    c.le
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
    xpsle.t
    xpsle.x
    xpsle.y
    xpsle.1
    xpsle.2
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
    xpsle.t
    xpsle.x
    xpsle.y
    xpsle.1
    xpsle.2
    @7
    @8
    @9
    xpslem
    wph
    @6
    @0
    @5
    wf1o
    #
    @6
    @0
    @5
    wfo
    @0
    @6
    @4
    wf1o
    @10
    wph
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
    mp1i
    @6
    @0
    @5
    f1ofo
    syl
    wph
    @1
    @2
    cprds
    ovexd
    xpsle.p
    imasless
end
