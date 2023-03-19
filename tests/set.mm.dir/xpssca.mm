include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
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
include "csca.mm"
include "wceq.mm"
include "wtru.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ovex.mm"
include "cnvex.mm"
include "prdssca.mm"
include "trud.mm"
include "imassca.mm"

theorem xpssca
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cG: class G
  let cV: class V
  let cW: class W
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vc: setvar c
  let cB: class B
  let vb: setvar b
  let cK: class K
  let cC: class C
  let cX: class X
  let c.x: class .x.
  let c.xp: class .X.
  let cY: class Y
  let c.xb: class .xb
  assume xpssca.t: |- T = ( R Xs. S )
  assume xpssca.g: |- G = ( Scalar ` R )
  assume xpssca.1: |- ( ph -> R e. V )
  assume xpssca.2: |- ( ph -> S e. W )


  assert |- ( ph -> G = ( Scalar ` T ) )

  proof
    wph
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cxp
    #
    cG
    cR
    csn
    #
    cS
    csn
    #
    ccda
    co
    #
    ccnv
    #
    cprds
    co
    #
    cT
    vx
    vy
    @0
    @1
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
    cG
    @8
    crn
    #
    cvv
    wph
    vx
    vy
    cR
    cS
    cT
    @7
    @8
    cG
    cV
    cW
    @0
    @1
    xpssca.t
    @0
    eqid
    #
    @1
    eqid
    #
    xpssca.1
    xpssca.2
    @8
    eqid
    #
    xpssca.g
    @7
    eqid
    #
    xpsval
    wph
    vx
    vy
    cR
    cS
    cT
    @7
    @8
    cG
    cV
    cW
    @0
    @1
    xpssca.t
    @11
    @12
    xpssca.1
    xpssca.2
    @13
    xpssca.g
    @14
    xpslem
    wph
    @10
    @2
    @9
    wf1o
    #
    @10
    @2
    @9
    wfo
    @2
    @10
    @8
    wf1o
    @15
    wph
    vx
    vy
    @0
    @1
    @8
    @13
    xpsff1o2
    @2
    @10
    @8
    f1ocnv
    mp1i
    @10
    @2
    @9
    f1ofo
    syl
    wph
    cG
    @6
    cprds
    ovexd
    cG
    @7
    csca
    cfv
    wceq
    wtru
    @7
    @6
    cG
    cvv
    cvv
    @14
    cG
    cvv
    wcel
    wtru
    cG
    cR
    csca
    cfv
    cvv
    xpssca.g
    cR
    csca
    fvex
    eqeltri
    a1i
    @6
    cvv
    wcel
    wtru
    @5
    @3
    @4
    ccda
    ovex
    cnvex
    a1i
    prdssca
    trud
    imassca
end
