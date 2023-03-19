include "corng.mm"
include "wcel.mm"
include "crg.mm"
include "cogrp.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wa.mm"
include "cmulr.mm"
include "co.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isorng.mm"
include "simp2bi.mm"

theorem orngogrp
  let cR: class R
  let va: setvar a
  let vb: setvar b


  assert |- ( R e. oRing -> R e. oGrp )

  proof
    cR
    corng
    wcel
    cR
    crg
    wcel
    cR
    cogrp
    wcel
    cR
    c0g
    cfv
    #
    va
    cv
    #
    cR
    cple
    cfv
    #
    wbr
    @0
    vb
    cv
    #
    @2
    wbr
    wa
    @0
    @1
    @3
    cR
    cmulr
    cfv
    #
    co
    @2
    wbr
    wi
    vb
    cR
    cbs
    cfv
    #
    wral
    va
    @5
    wral
    @5
    cR
    @4
    @2
    @0
    va
    vb
    @5
    eqid
    @0
    eqid
    @4
    eqid
    @2
    eqid
    isorng
    simp2bi
end
