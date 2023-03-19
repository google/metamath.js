include "cnbgr.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cusgr.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "ovex.mm"
include "nbusgrf1o.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"

theorem nbedgusgr
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vf: setvar f
  assume nbusgrf1o.v: |- V = ( Vtx ` G )
  assume nbusgrf1o.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint U e
  disjoint E c
  disjoint E f
  disjoint c e
  disjoint c f
  disjoint e f
  disjoint G c
  disjoint G f
  disjoint U c
  disjoint U f
  disjoint V c
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( # ` ( G NeighbVtx U ) ) = ( # ` { e e. E | U e. e } ) )

  proof
    cG
    cU
    cnbgr
    co
    #
    cvv
    wcel
    cG
    cusgr
    wcel
    cU
    cV
    wcel
    wa
    @0
    cU
    ve
    cv
    wcel
    ve
    cE
    crab
    #
    vf
    cv
    wf1o
    vf
    wex
    @0
    chash
    cfv
    @1
    chash
    cfv
    wceq
    cG
    cU
    cnbgr
    ovex
    cU
    ve
    vf
    cE
    cG
    cV
    nbusgrf1o.v
    nbusgrf1o.e
    nbusgrf1o
    @0
    @1
    vf
    cvv
    hasheqf1oi
    mpsyl
end
