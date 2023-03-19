include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cdm.mm"
include "cxp.mm"
include "wfo.mm"
include "eqid.mm"
include "opidonOLD.mm"
include "wceq.mm"
include "crn.mm"
include "forn.mm"
include "syl5req.mm"
include "wb.mm"
include "xpeq12.mm"
include "anidms.mm"
include "foeq2.mm"
include "syl.mm"
include "foeq3.mm"
include "bitrd.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem opidon2OLD
  let cG: class G
  let cX: class X
  assume opidon2OLD.1: |- X = ran G


  assert |- ( G e. ( Magma i^i ExId ) -> G : ( X X. X ) -onto-> X )

  proof
    cG
    cmagm
    cexid
    cin
    wcel
    cG
    cdm
    cdm
    #
    @0
    cxp
    #
    @0
    cG
    wfo
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wfo
    #
    cG
    @0
    @0
    eqid
    opidonOLD
    @0
    cX
    wceq
    #
    @2
    @4
    @2
    cX
    cG
    crn
    @0
    opidon2OLD.1
    @1
    @0
    cG
    forn
    syl5req
    @5
    @2
    @4
    @5
    @2
    @3
    @0
    cG
    wfo
    #
    @4
    @5
    @1
    @3
    wceq
    #
    @2
    @6
    wb
    @5
    @7
    @0
    cX
    @0
    cX
    xpeq12
    anidms
    @1
    @3
    @0
    cG
    foeq2
    syl
    @0
    cX
    @3
    cG
    foeq3
    bitrd
    biimpd
    mpcom
    syl
end
