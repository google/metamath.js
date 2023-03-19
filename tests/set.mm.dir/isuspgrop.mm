include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cuspgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "eqid.mm"
include "isuspgr.mm"
include "mp1i.mm"
include "opiedgfv.mm"
include "dmeqd.mm"
include "opvtxfv.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "rabeqdv.mm"
include "f1eq123d.mm"
include "bitrd.mm"

theorem isuspgrop
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let vp: setvar p

  disjoint E p
  disjoint V p
  disjoint W p
  disjoint X p
  assert |- ( ( V e. W /\ E e. X ) -> ( <. V , E >. e. USPGraph <-> E : dom E -1-1-> { p e. ( ~P V \ { (/) } ) | ( # ` p ) <_ 2 } ) )

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
    cuspgr
    wcel
    #
    @1
    ciedg
    cfv
    #
    cdm
    #
    vp
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vp
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
    crab
    #
    @3
    wf1
    #
    cE
    cdm
    #
    @5
    vp
    cV
    cpw
    #
    @8
    cdif
    #
    crab
    #
    cE
    wf1
    @1
    cvv
    wcel
    @2
    @11
    wb
    @0
    cV
    cE
    opex
    vp
    cvv
    @3
    @1
    @6
    @6
    eqid
    @3
    eqid
    isuspgr
    mp1i
    @0
    @4
    @12
    @10
    @15
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
    @16
    dmeqd
    @0
    @5
    vp
    @9
    @14
    @0
    @7
    @13
    @8
    @0
    @6
    cV
    cE
    cV
    cW
    cX
    opvtxfv
    pweqd
    difeq1d
    rabeqdv
    f1eq123d
    bitrd
end
