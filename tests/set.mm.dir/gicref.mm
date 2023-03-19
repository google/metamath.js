include "cgrp.mm"
include "wcel.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "cgim.mm"
include "co.mm"
include "cgic.mm"
include "wbr.mm"
include "cghm.mm"
include "ccnv.mm"
include "eqid.mm"
include "idghm.mm"
include "cnvresid.mm"
include "syl5eqel.mm"
include "isgim2.mm"
include "sylanbrc.mm"
include "brgici.mm"
include "syl.mm"

theorem gicref
  let cR: class R


  assert |- ( R e. Grp -> R ~=g R )

  proof
    cR
    cgrp
    wcel
    #
    cid
    cR
    cbs
    cfv
    #
    cres
    #
    cR
    cR
    cgim
    co
    wcel
    #
    cR
    cR
    cgic
    wbr
    @0
    @2
    cR
    cR
    cghm
    co
    #
    wcel
    @2
    ccnv
    #
    @4
    wcel
    @3
    @1
    cR
    @1
    eqid
    idghm
    #
    @0
    @5
    @2
    @4
    @1
    cnvresid
    @6
    syl5eqel
    cR
    cR
    @2
    isgim2
    sylanbrc
    cR
    cR
    @2
    brgici
    syl
end
