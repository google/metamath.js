include "wcel.mm"
include "cgrp.mm"
include "cngp.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "tngbas.mm"
include "eqidd.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "tngplusg.mm"
include "eqcomd.mm"
include "oveqdr.mm"
include "grppropd.mm"
include "biimpd.mm"
include "ngpgrp.mm"
include "impel.mm"

theorem tnggrpr
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngngp3.t: |- T = ( G toNrmGrp N )


  assert |- ( ( N e. V /\ T e. NrmGrp ) -> G e. Grp )

  proof
    cN
    cV
    wcel
    #
    cT
    cgrp
    wcel
    #
    cG
    cgrp
    wcel
    #
    cT
    cngp
    wcel
    @0
    @1
    @2
    @0
    vx
    vy
    cG
    cbs
    cfv
    #
    cT
    cG
    @3
    cT
    cG
    cN
    cV
    tngngp3.t
    @3
    eqid
    tngbas
    @0
    @3
    eqidd
    @0
    vx
    cv
    @3
    wcel
    vy
    cv
    @3
    wcel
    wa
    vx
    vy
    cT
    cplusg
    cfv
    #
    cG
    cplusg
    cfv
    #
    @0
    @5
    @4
    @5
    cT
    cG
    cN
    cV
    tngngp3.t
    @5
    eqid
    tngplusg
    eqcomd
    oveqdr
    grppropd
    biimpd
    cT
    ngpgrp
    impel
end
