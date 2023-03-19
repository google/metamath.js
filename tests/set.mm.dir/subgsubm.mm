include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cv.mm"
include "cminusg.mm"
include "wral.mm"
include "wa.mm"
include "cgrp.mm"
include "wb.mm"
include "subgrcl.mm"
include "eqid.mm"
include "issubg3.mm"
include "syl.mm"
include "ibi.mm"
include "simpld.mm"

theorem subgsubm
  let cS: class S
  let cG: class G
  let vx: setvar x


  assert |- ( S e. ( SubGrp ` G ) -> S e. ( SubMnd ` G ) )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cS
    cG
    csubmnd
    cfv
    wcel
    #
    vx
    cv
    cG
    cminusg
    cfv
    #
    cfv
    cS
    wcel
    vx
    cS
    wral
    #
    @0
    @1
    @3
    wa
    #
    @0
    cG
    cgrp
    wcel
    @0
    @4
    wb
    cS
    cG
    subgrcl
    vx
    cS
    cG
    @2
    @2
    eqid
    issubg3
    syl
    ibi
    simpld
end
