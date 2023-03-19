include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "cnbgr.mm"
include "co.mm"
include "eqid.mm"
include "eleq2.mm"
include "cbvrabv.mm"
include "nbusgrf1o1.mm"

theorem nbusgrf1o
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  assume nbusgrf1o.v: |- V = ( Vtx ` G )
  assume nbusgrf1o.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint E f
  disjoint e f
  disjoint G f
  disjoint U e
  disjoint U f
  disjoint E c
  disjoint c e
  disjoint c f
  disjoint G c
  disjoint U c
  disjoint V c
  assert |- ( ( G e. USGraph /\ U e. V ) -> E. f f : ( G NeighbVtx U ) -1-1-onto-> { e e. E | U e. e } )

  proof
    cU
    vc
    vf
    cE
    cG
    cU
    ve
    cv
    #
    wcel
    #
    ve
    cE
    crab
    cG
    cU
    cnbgr
    co
    #
    cV
    nbusgrf1o.v
    nbusgrf1o.e
    @2
    eqid
    @1
    cU
    vc
    cv
    #
    wcel
    ve
    vc
    cE
    @0
    @3
    cU
    eleq2
    cbvrabv
    nbusgrf1o1
end
