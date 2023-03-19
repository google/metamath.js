include "cngp.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cnm.mm"
include "csg.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "eqid.mm"
include "tngds.mm"
include "ax-mp.mm"
include "cgrp.mm"
include "cmt.mm"
include "isngp2.mm"
include "simp3bi.mm"
include "syl5eqr.mm"

theorem nrmtngdist
  let cT: class T
  let cG: class G
  let cX: class X
  assume nrmtngdist.t: |- T = ( G toNrmGrp ( norm ` G ) )
  assume nrmtngdist.x: |- X = ( Base ` G )


  assert |- ( G e. NrmGrp -> ( dist ` T ) = ( ( dist ` G ) |` ( X X. X ) ) )

  proof
    cG
    cngp
    wcel
    #
    cT
    cds
    cfv
    #
    cG
    cnm
    cfv
    #
    cG
    csg
    cfv
    #
    ccom
    #
    cG
    cds
    cfv
    #
    cX
    cX
    cxp
    cres
    #
    @2
    cvv
    wcel
    @4
    @1
    wceq
    cG
    cnm
    fvex
    cT
    cG
    @3
    @2
    cvv
    nrmtngdist.t
    @3
    eqid
    #
    tngds
    ax-mp
    @0
    cG
    cgrp
    wcel
    cG
    cmt
    wcel
    @4
    @6
    wceq
    @5
    @6
    cG
    @3
    @2
    cX
    @2
    eqid
    @7
    @5
    eqid
    nrmtngdist.x
    @6
    eqid
    isngp2
    simp3bi
    syl5eqr
end
