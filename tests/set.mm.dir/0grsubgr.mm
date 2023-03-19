include "wcel.mm"
include "c0.mm"
include "csubgr.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cpw.mm"
include "w3a.mm"
include "0ss.mm"
include "dm0.mm"
include "reseq2i.mm"
include "res0.mm"
include "eqtr2i.mm"
include "3pm3.2i.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "vtxval0.mm"
include "eqcomi.mm"
include "eqid.mm"
include "iedgval0.mm"
include "cedg.mm"
include "crn.mm"
include "edgval.mm"
include "rneqi.mm"
include "rn0.mm"
include "3eqtrri.mm"
include "issubgr.mm"
include "mpan2.mm"
include "mpbiri.mm"

theorem 0grsubgr
  let cG: class G
  let cW: class W


  assert |- ( G e. W -> (/) SubGraph G )

  proof
    cG
    cW
    wcel
    #
    c0
    cG
    csubgr
    wbr
    #
    c0
    cG
    cvtx
    cfv
    #
    wss
    #
    c0
    cG
    ciedg
    cfv
    #
    c0
    cdm
    #
    cres
    #
    wceq
    #
    c0
    c0
    cpw
    #
    wss
    #
    w3a
    #
    @3
    @7
    @9
    @2
    0ss
    @6
    @4
    c0
    cres
    c0
    @5
    c0
    @4
    dm0
    reseq2i
    @4
    res0
    eqtr2i
    @8
    0ss
    3pm3.2i
    @0
    c0
    cvv
    wcel
    @1
    @10
    wb
    0ex
    @2
    @4
    c0
    cvv
    c0
    cG
    c0
    c0
    cW
    c0
    cvtx
    cfv
    c0
    vtxval0
    eqcomi
    @2
    eqid
    c0
    ciedg
    cfv
    #
    c0
    iedgval0
    eqcomi
    @4
    eqid
    c0
    cedg
    cfv
    @11
    crn
    c0
    crn
    c0
    c0
    edgval
    @11
    c0
    iedgval0
    rneqi
    rn0
    3eqtrri
    issubgr
    mpan2
    mpbiri
end
