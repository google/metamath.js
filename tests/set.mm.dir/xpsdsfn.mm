include "cxp.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cprds.mm"
include "cds.mm"
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
include "a1i.mm"
include "f1ocnv.mm"
include "f1ofo.mm"
include "3syl.mm"
include "ovexd.mm"
include "imasdsfn.mm"

theorem xpsdsfn
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


  assert |- ( ph -> P Fn ( ( X X. Y ) X. ( X X. Y ) ) )

  proof
    wph
    cX
    cY
    cxp
    #
    cP
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
    @3
    cds
    cfv
    #
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
    @5
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
    @5
    @1
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    @5
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
    @5
    @1
    cV
    cW
    cX
    cY
    xpsds.t
    xpsds.x
    xpsds.y
    xpsds.1
    xpsds.2
    @8
    @9
    @10
    xpslem
    wph
    @0
    @7
    @5
    wf1o
    #
    @7
    @0
    @6
    wf1o
    @7
    @0
    @6
    wfo
    @11
    wph
    vx
    vy
    cX
    cY
    @5
    @8
    xpsff1o2
    a1i
    @0
    @7
    @5
    f1ocnv
    @7
    @0
    @6
    f1ofo
    3syl
    wph
    @1
    @2
    cprds
    ovexd
    @4
    eqid
    xpsds.p
    imasdsfn
end
