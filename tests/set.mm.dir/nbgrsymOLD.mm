include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cv.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "wb.mm"
include "ancom.mm"
include "necom.mm"
include "prcom.mm"
include "sseq1i.mm"
include "rexbii.mm"
include "3anbi123i.mm"
include "a1i.mm"
include "eqid.mm"
include "nbgrelOLD.mm"
include "3bitr4d.mm"

theorem nbgrsymOLD
  let cG: class G
  let cK: class K
  let cN: class N
  let cW: class W
  let ve: setvar e


  assert |- ( G e. W -> ( N e. ( G NeighbVtx K ) <-> K e. ( G NeighbVtx N ) ) )

  proof
    cG
    cW
    wcel
    #
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    cK
    @1
    wcel
    #
    wa
    #
    cN
    cK
    wne
    #
    cK
    cN
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    w3a
    #
    @3
    @2
    wa
    #
    cK
    cN
    wne
    #
    cN
    cK
    cpr
    #
    @7
    wss
    #
    ve
    @9
    wrex
    #
    w3a
    #
    cN
    cG
    cK
    cnbgr
    co
    wcel
    cK
    cG
    cN
    cnbgr
    co
    wcel
    @11
    @17
    wb
    @0
    @4
    @12
    @5
    @13
    @10
    @16
    @2
    @3
    ancom
    cN
    cK
    necom
    @8
    @15
    ve
    @9
    @6
    @14
    @7
    cK
    cN
    prcom
    sseq1i
    rexbii
    3anbi123i
    a1i
    ve
    @9
    cG
    cN
    cK
    @1
    cW
    @1
    eqid
    #
    @9
    eqid
    #
    nbgrelOLD
    ve
    @9
    cG
    cK
    cN
    @1
    cW
    @18
    @19
    nbgrelOLD
    3bitr4d
end
