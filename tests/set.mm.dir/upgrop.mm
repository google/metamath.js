include "cupgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "ciedg.mm"
include "cop.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "eqid.mm"
include "upgrf.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "opex.mm"
include "isupgr.mm"
include "mp1i.mm"
include "opiedgfv.mm"
include "dmeqd.mm"
include "opvtxfv.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "rabeqdv.mm"
include "feq123d.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem upgrop
  let cG: class G
  let vp: setvar p


  assert |- ( G e. UPGraph -> <. ( Vtx ` G ) , ( iEdg ` G ) >. e. UPGraph )

  proof
    cG
    cupgr
    wcel
    #
    cG
    cvtx
    cfv
    #
    cG
    ciedg
    cfv
    #
    cop
    #
    cupgr
    wcel
    #
    @2
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
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    @2
    wf
    #
    vp
    @2
    cG
    @1
    @1
    eqid
    @2
    eqid
    upgrf
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    #
    @4
    @11
    wb
    @0
    @12
    @13
    cG
    cvtx
    fvex
    cG
    ciedg
    fvex
    pm3.2i
    @14
    @4
    @3
    ciedg
    cfv
    #
    cdm
    #
    @6
    vp
    @3
    cvtx
    cfv
    #
    cpw
    #
    @8
    cdif
    #
    crab
    #
    @15
    wf
    #
    @11
    @3
    cvv
    wcel
    @4
    @21
    wb
    @14
    @1
    @2
    opex
    vp
    cvv
    @15
    @3
    @17
    @17
    eqid
    @15
    eqid
    isupgr
    mp1i
    @14
    @16
    @5
    @20
    @10
    @15
    @2
    @2
    @1
    cvv
    cvv
    opiedgfv
    #
    @14
    @15
    @2
    @22
    dmeqd
    @14
    @6
    vp
    @19
    @9
    @14
    @18
    @7
    @8
    @14
    @17
    @1
    @2
    @1
    cvv
    cvv
    opvtxfv
    pweqd
    difeq1d
    rabeqdv
    feq123d
    bitrd
    mp1i
    mpbird
end
