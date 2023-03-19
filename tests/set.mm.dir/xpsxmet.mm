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
include "cres.mm"
include "cvv.mm"
include "eqid.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wf1o.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "ovexd.mm"
include "cxmt.mm"
include "wcel.mm"
include "wss.mm"
include "xpsxmetlem.mm"
include "ssid.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "imasf1oxmet.mm"

theorem xpsxmet
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xpsds.t: |- T = ( R Xs. S )
  assume xpsds.x: |- X = ( Base ` R )
  assume xpsds.y: |- Y = ( Base ` S )
  assume xpsds.1: |- ( ph -> R e. V )
  assume xpsds.2: |- ( ph -> S e. W )
  assume xpsds.p: |- P = ( dist ` T )
  assume xpsds.m: |- M = ( ( dist ` R ) |` ( X X. X ) )
  assume xpsds.n: |- N = ( ( dist ` S ) |` ( Y X. Y ) )
  assume xpsds.3: |- ( ph -> M e. ( *Met ` X ) )
  assume xpsds.4: |- ( ph -> N e. ( *Met ` Y ) )


  assert |- ( ph -> P e. ( *Met ` ( X X. Y ) ) )

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
    crn
    #
    @6
    cxp
    cres
    #
    @5
    ccnv
    #
    @6
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
    @9
    @10
    @11
    xpslem
    @0
    @6
    @5
    wf1o
    @6
    @0
    @8
    wf1o
    wph
    vx
    vy
    cX
    cY
    @5
    @9
    xpsff1o2
    @0
    @6
    @5
    f1ocnv
    mp1i
    wph
    @1
    @2
    cprds
    ovexd
    @7
    eqid
    xpsds.p
    wph
    @4
    @6
    cxmt
    cfv
    #
    wcel
    @6
    @6
    wss
    @7
    @12
    wcel
    wph
    vx
    vy
    cP
    cR
    cS
    cT
    cM
    cN
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
    xpsds.m
    xpsds.n
    xpsds.3
    xpsds.4
    xpsxmetlem
    @6
    ssid
    @4
    @6
    @6
    xmetres2
    sylancl
    imasf1oxmet
end
