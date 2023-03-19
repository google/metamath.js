include "clnm.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "clmhm.mm"
include "co.mm"
include "crn.mm"
include "wceq.mm"
include "clmod.mm"
include "cvv.mm"
include "lnmlmod.mm"
include "snex.mm"
include "eqid.mm"
include "pwsdiaglmhm.mm"
include "sylancl.mm"
include "id.mm"
include "wf1o.mm"
include "wfo.mm"
include "vex.mm"
include "pwssnf1o.mm"
include "mpan2.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "lnmepi.mm"
include "syl3anc.mm"

theorem pwslnmlem1
  let vi: setvar i
  let cW: class W
  let cY: class Y
  let vx: setvar x
  assume pwslnmlem1.y: |- Y = ( W ^s { i } )

  disjoint W i
  disjoint Y x
  disjoint W x
  disjoint i x
  assert |- ( W e. LNoeM -> Y e. LNoeM )

  proof
    cW
    clnm
    wcel
    #
    vx
    cW
    cbs
    cfv
    #
    vi
    cv
    #
    csn
    #
    vx
    cv
    csn
    cxp
    cmpt
    #
    cW
    cY
    clmhm
    co
    wcel
    #
    @0
    @4
    crn
    cY
    cbs
    cfv
    #
    wceq
    #
    cY
    clnm
    wcel
    @0
    cW
    clmod
    wcel
    @3
    cvv
    wcel
    @5
    cW
    lnmlmod
    @2
    snex
    vx
    @1
    cW
    @4
    @3
    cvv
    cY
    pwslnmlem1.y
    @1
    eqid
    #
    @4
    eqid
    #
    pwsdiaglmhm
    sylancl
    @0
    id
    @0
    @1
    @6
    @4
    wf1o
    #
    @1
    @6
    @4
    wfo
    @7
    @0
    @2
    cvv
    wcel
    @10
    vi
    vex
    vx
    @1
    @6
    cW
    @4
    @2
    clnm
    cvv
    cY
    pwslnmlem1.y
    @8
    @9
    @6
    eqid
    #
    pwssnf1o
    mpan2
    @1
    @6
    @4
    f1ofo
    @1
    @6
    @4
    forn
    3syl
    @6
    cW
    cY
    @4
    @11
    lnmepi
    syl3anc
end
