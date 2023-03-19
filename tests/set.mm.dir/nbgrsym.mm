include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
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
include "ancom.mm"
include "necom.mm"
include "prcom.mm"
include "sseq1i.mm"
include "rexbii.mm"
include "3anbi123i.mm"
include "eqid.mm"
include "nbgrel.mm"
include "3bitr4i.mm"

theorem nbgrsym
  let cG: class G
  let cK: class K
  let cN: class N
  let ve: setvar e


  assert |- ( N e. ( G NeighbVtx K ) <-> K e. ( G NeighbVtx N ) )

  proof
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    cK
    @0
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
    @2
    @1
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
    @6
    wss
    #
    ve
    @8
    wrex
    #
    w3a
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
    @3
    @10
    @4
    @11
    @9
    @14
    @1
    @2
    ancom
    cN
    cK
    necom
    @7
    @13
    ve
    @8
    @5
    @12
    @6
    cK
    cN
    prcom
    sseq1i
    rexbii
    3anbi123i
    ve
    @8
    cG
    cN
    @0
    cK
    @0
    eqid
    #
    @8
    eqid
    #
    nbgrel
    ve
    @8
    cG
    cK
    @0
    cN
    @15
    @16
    nbgrel
    3bitr4i
end
