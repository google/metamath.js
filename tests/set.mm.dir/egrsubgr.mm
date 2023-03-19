include "wcel.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "wfun.mm"
include "cedg.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "csubgr.mm"
include "wbr.mm"
include "cdm.mm"
include "cres.mm"
include "cpw.mm"
include "simp2.mm"
include "wb.mm"
include "eqid.mm"
include "edg0iedg0.mm"
include "adantl.mm"
include "res0.mm"
include "eqcomi.mm"
include "id.mm"
include "dmeq.mm"
include "dm0.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "3eqtr4a.mm"
include "syl6bi.mm"
include "impr.mm"
include "3adant2.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "3ad2ant3.mm"
include "issubgr.mm"
include "3ad2ant1.mm"
include "mpbir3and.mm"

theorem egrsubgr
  let cS: class S
  let cU: class U
  let cG: class G
  let cW: class W


  assert |- ( ( ( G e. W /\ S e. U ) /\ ( Vtx ` S ) C_ ( Vtx ` G ) /\ ( Fun ( iEdg ` S ) /\ ( Edg ` S ) = (/) ) ) -> S SubGraph G )

  proof
    cG
    cW
    wcel
    cS
    cU
    wcel
    wa
    #
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wss
    #
    cS
    ciedg
    cfv
    #
    wfun
    #
    cS
    cedg
    cfv
    #
    c0
    wceq
    #
    wa
    #
    w3a
    cS
    cG
    csubgr
    wbr
    #
    @3
    @4
    cG
    ciedg
    cfv
    #
    @4
    cdm
    #
    cres
    #
    wceq
    #
    @6
    @1
    cpw
    #
    wss
    #
    @0
    @3
    @8
    simp2
    @0
    @8
    @13
    @3
    @0
    @5
    @7
    @13
    @0
    @5
    wa
    @7
    @4
    c0
    wceq
    #
    @13
    @5
    @7
    @16
    wb
    @0
    @6
    cS
    @4
    @4
    eqid
    #
    @6
    eqid
    #
    edg0iedg0
    adantl
    @16
    c0
    @10
    c0
    cres
    #
    @4
    @12
    @19
    c0
    @10
    res0
    eqcomi
    @16
    id
    @16
    @11
    c0
    @10
    @16
    @11
    c0
    cdm
    c0
    @4
    c0
    dmeq
    dm0
    syl6eq
    reseq2d
    3eqtr4a
    syl6bi
    impr
    3adant2
    @8
    @0
    @15
    @3
    @7
    @15
    @5
    @7
    @15
    c0
    @14
    wss
    @14
    0ss
    @6
    c0
    @14
    sseq1
    mpbiri
    adantl
    3ad2ant3
    @0
    @3
    @9
    @3
    @13
    @15
    w3a
    wb
    @8
    @2
    @10
    cS
    cU
    @6
    cG
    @4
    @1
    cW
    @1
    eqid
    @2
    eqid
    @17
    @10
    eqid
    @18
    issubgr
    3ad2ant1
    mpbir3and
end
