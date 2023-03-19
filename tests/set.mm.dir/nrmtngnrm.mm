include "cngp.mm"
include "wcel.mm"
include "cnm.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "cds.mm"
include "cbs.mm"
include "cme.mm"
include "ngpgrp.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "nrmtngdist.mm"
include "cmt.mm"
include "csg.mm"
include "ccom.mm"
include "w3a.mm"
include "isngp2.mm"
include "msmet.mm"
include "3ad2ant2.mm"
include "sylbi.mm"
include "eqeltrd.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "wb.mm"
include "nmf.mm"
include "tngngp2.mm"
include "syl.mm"
include "mpbir2and.mm"
include "jca.mm"
include "reex.mm"
include "tngnm.mm"
include "eqcomd.mm"

theorem nrmtngnrm
  let cT: class T
  let cG: class G
  assume nrmtngdist.t: |- T = ( G toNrmGrp ( norm ` G ) )


  assert |- ( G e. NrmGrp -> ( T e. NrmGrp /\ ( norm ` T ) = ( norm ` G ) ) )

  proof
    cG
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cT
    cnm
    cfv
    #
    cG
    cnm
    cfv
    #
    wceq
    @0
    @1
    cG
    cgrp
    wcel
    #
    cT
    cds
    cfv
    #
    cG
    cbs
    cfv
    #
    cme
    cfv
    #
    wcel
    #
    cG
    ngpgrp
    #
    @0
    @5
    cG
    cds
    cfv
    #
    @6
    @6
    cxp
    cres
    #
    @7
    cT
    cG
    @6
    nrmtngdist.t
    @6
    eqid
    #
    nrmtngdist
    @0
    @4
    cG
    cmt
    wcel
    #
    @3
    cG
    csg
    cfv
    #
    ccom
    @11
    wceq
    #
    w3a
    @11
    @7
    wcel
    #
    @10
    @11
    cG
    @14
    @3
    @6
    @3
    eqid
    #
    @14
    eqid
    @10
    eqid
    @12
    @11
    eqid
    #
    isngp2
    @13
    @4
    @16
    @15
    @11
    cG
    @6
    @12
    @18
    msmet
    3ad2ant2
    sylbi
    eqeltrd
    @0
    @6
    cr
    @3
    wf
    #
    @1
    @4
    @8
    wa
    wb
    cG
    @3
    @6
    @12
    @17
    nmf
    #
    @5
    cT
    cG
    @3
    @6
    nrmtngdist.t
    @12
    @5
    eqid
    tngngp2
    syl
    mpbir2and
    @0
    @3
    @2
    @0
    @4
    @19
    wa
    @3
    @2
    wceq
    @0
    @4
    @19
    @9
    @20
    jca
    cr
    cT
    cG
    @3
    @6
    nrmtngdist.t
    @12
    reex
    tngnm
    syl
    eqcomd
    jca
end
