include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cv.mm"
include "wss.mm"
include "cedg.mm"
include "cfv.mm"
include "wrex.mm"
include "w3a.mm"
include "eqid.mm"
include "nbgrelOLD.mm"
include "simp1l.mm"
include "syl6bi.mm"
include "imp.mm"

theorem nbgrisvtxOLD
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vn: setvar n
  assume nbgrisvtx.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. W /\ N e. ( G NeighbVtx K ) ) -> N e. V )

  proof
    cG
    cW
    wcel
    #
    cN
    cG
    cK
    cnbgr
    co
    wcel
    #
    cN
    cV
    wcel
    #
    @0
    @1
    @2
    cK
    cV
    wcel
    #
    wa
    cN
    cK
    wne
    #
    cK
    cN
    cpr
    ve
    cv
    wss
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    w3a
    @2
    ve
    @5
    cG
    cN
    cK
    cV
    cW
    nbgrisvtx.v
    @5
    eqid
    nbgrelOLD
    @2
    @3
    @4
    @6
    simp1l
    syl6bi
    imp
end
