include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "eqid.mm"
include "issubg.mm"
include "simp1bi.mm"

theorem subgrcl
  let cS: class S
  let cG: class G


  assert |- ( S e. ( SubGrp ` G ) -> G e. Grp )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    cG
    cgrp
    wcel
    cS
    cG
    cbs
    cfv
    #
    wss
    cG
    cS
    cress
    co
    cgrp
    wcel
    @0
    cS
    cG
    @0
    eqid
    issubg
    simp1bi
end
