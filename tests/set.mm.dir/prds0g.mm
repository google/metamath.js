include "c0g.mm"
include "cfv.mm"
include "ccom.mm"
include "cbs.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cvv.mm"
include "eqid.mm"
include "elex.mm"
include "syl.mm"
include "prdsidlem.mm"
include "cmnd.mm"
include "wrex.mm"
include "prdsmndd.mm"
include "mndid.mm"
include "ismgmid.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem prds0g
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vc: setvar c
  assume prdsmndd.y: |- Y = ( S Xs_ R )
  assume prdsmndd.i: |- ( ph -> I e. W )
  assume prdsmndd.s: |- ( ph -> S e. V )
  assume prdsmndd.r: |- ( ph -> R : I --> Mnd )


  assert |- ( ph -> ( 0g o. R ) = ( 0g ` Y ) )

  proof
    wph
    cY
    c0g
    cfv
    #
    c0g
    cR
    ccom
    #
    wph
    @1
    cY
    cbs
    cfv
    #
    wcel
    @1
    vb
    cv
    #
    cY
    cplusg
    cfv
    #
    co
    @3
    wceq
    @3
    @1
    @4
    co
    @3
    wceq
    wa
    vb
    @2
    wral
    wa
    @0
    @1
    wceq
    wph
    vb
    @2
    @4
    cR
    cS
    cI
    cvv
    cvv
    cY
    @1
    prdsmndd.y
    @2
    eqid
    #
    @4
    eqid
    #
    wph
    cS
    cV
    wcel
    cS
    cvv
    wcel
    prdsmndd.s
    cS
    cV
    elex
    syl
    wph
    cI
    cW
    wcel
    cI
    cvv
    wcel
    prdsmndd.i
    cI
    cW
    elex
    syl
    prdsmndd.r
    @1
    eqid
    prdsidlem
    wph
    vb
    @2
    @4
    @1
    va
    cY
    @0
    @5
    @0
    eqid
    @6
    wph
    cY
    cmnd
    wcel
    va
    cv
    #
    @3
    @4
    co
    @3
    wceq
    @3
    @7
    @4
    co
    @3
    wceq
    wa
    vb
    @2
    wral
    va
    @2
    wrex
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdsmndd.y
    prdsmndd.i
    prdsmndd.s
    prdsmndd.r
    prdsmndd
    vb
    va
    @2
    @4
    cY
    @5
    @6
    mndid
    syl
    ismgmid
    mpbid
    eqcomd
end
