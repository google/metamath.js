include "cusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "crab.mm"
include "rabfi.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "edgusgrnbfin.mm"
include "3adant2.mm"
include "mpbird.mm"

theorem nbusgrfi
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  assume nbusgrf1o.v: |- V = ( Vtx ` G )
  assume nbusgrf1o.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ E e. Fin /\ U e. V ) -> ( G NeighbVtx U ) e. Fin )

  proof
    cG
    cusgr
    wcel
    #
    cE
    cfn
    wcel
    #
    cU
    cV
    wcel
    #
    w3a
    cG
    cU
    cnbgr
    co
    cfn
    wcel
    #
    cU
    ve
    cv
    wcel
    #
    ve
    cE
    crab
    cfn
    wcel
    #
    @1
    @0
    @5
    @2
    @4
    ve
    cE
    rabfi
    3ad2ant2
    @0
    @2
    @3
    @5
    wb
    @1
    cU
    ve
    cE
    cG
    cV
    nbusgrf1o.v
    nbusgrf1o.e
    edgusgrnbfin
    3adant2
    mpbird
end
