include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "eqid.mm"
include "txval.mm"
include "ctb.mm"
include "topbas.mm"
include "txbas.mm"
include "syl2an.mm"
include "tgcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem txtop
  let cR: class R
  let cS: class S
  let vu: setvar u
  let vv: setvar v


  assert |- ( ( R e. Top /\ S e. Top ) -> ( R tX S ) e. Top )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    vu
    vv
    cR
    cS
    vu
    cv
    vv
    cv
    cxp
    cmpt2
    crn
    #
    ctg
    cfv
    #
    ctop
    vu
    vv
    @3
    cR
    cS
    ctop
    ctop
    @3
    eqid
    #
    txval
    @2
    @3
    ctb
    wcel
    #
    @4
    ctop
    wcel
    @0
    cR
    ctb
    wcel
    cS
    ctb
    wcel
    @6
    @1
    cR
    topbas
    cS
    topbas
    vu
    vv
    @3
    cR
    cS
    @5
    txbas
    syl2an
    @3
    tgcl
    syl
    eqeltrd
end
