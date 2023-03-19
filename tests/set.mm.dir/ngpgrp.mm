include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmt.mm"
include "cnm.mm"
include "cfv.mm"
include "csg.mm"
include "ccom.mm"
include "cds.mm"
include "wss.mm"
include "eqid.mm"
include "isngp.mm"
include "simp1bi.mm"

theorem ngpgrp
  let cG: class G


  assert |- ( G e. NrmGrp -> G e. Grp )

  proof
    cG
    cngp
    wcel
    cG
    cgrp
    wcel
    cG
    cmt
    wcel
    cG
    cnm
    cfv
    #
    cG
    csg
    cfv
    #
    ccom
    cG
    cds
    cfv
    #
    wss
    @2
    cG
    @1
    @0
    @0
    eqid
    @1
    eqid
    @2
    eqid
    isngp
    simp1bi
end
