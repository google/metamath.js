include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cuhgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "eqid.mm"
include "isuhgr.mm"
include "mp1i.mm"
include "opiedgfv.mm"
include "dmeqd.mm"
include "opvtxfv.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "feq123d.mm"
include "bitrd.mm"

theorem isuhgrop
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( V e. W /\ E e. X ) -> ( <. V , E >. e. UHGraph <-> E : dom E --> ( ~P V \ { (/) } ) ) )

  proof
    cV
    cW
    wcel
    cE
    cX
    wcel
    wa
    #
    cV
    cE
    cop
    #
    cuhgr
    wcel
    #
    @1
    ciedg
    cfv
    #
    cdm
    #
    @1
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    #
    cdif
    #
    @3
    wf
    #
    cE
    cdm
    #
    cV
    cpw
    #
    @7
    cdif
    #
    cE
    wf
    @1
    cvv
    wcel
    @2
    @9
    wb
    @0
    cV
    cE
    opex
    cvv
    @3
    @1
    @5
    @5
    eqid
    @3
    eqid
    isuhgr
    mp1i
    @0
    @4
    @10
    @8
    @12
    @3
    cE
    cE
    cV
    cW
    cX
    opiedgfv
    #
    @0
    @3
    cE
    @13
    dmeqd
    @0
    @6
    @11
    @7
    @0
    @5
    cV
    cE
    cV
    cW
    cX
    opvtxfv
    pweqd
    difeq1d
    feq123d
    bitrd
end
