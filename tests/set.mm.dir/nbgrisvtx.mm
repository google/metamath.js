include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
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
include "nbgrel.mm"
include "simp1l.mm"
include "sylbi.mm"

theorem nbgrisvtx
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let ve: setvar e
  assume nbgrisvtx.v: |- V = ( Vtx ` G )


  assert |- ( N e. ( G NeighbVtx K ) -> N e. V )

  proof
    cN
    cG
    cK
    cnbgr
    co
    wcel
    cN
    cV
    wcel
    #
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
    @0
    ve
    @3
    cG
    cN
    cV
    cK
    nbgrisvtx.v
    @3
    eqid
    nbgrel
    @0
    @1
    @2
    @4
    simp1l
    sylbi
end
