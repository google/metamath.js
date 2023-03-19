include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cfn.mm"
include "cv.mm"
include "crab.mm"
include "wf1o.mm"
include "wex.mm"
include "wi.mm"
include "nbusgrf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "fofi.mm"
include "expcom.mm"
include "syl.mm"
include "exlimiv.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1fi.mm"
include "impbid.mm"

theorem edgusgrnbfin
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
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( ( G NeighbVtx U ) e. Fin <-> { e e. E | U e. e } e. Fin ) )

  proof
    cG
    cusgr
    wcel
    cU
    cV
    wcel
    wa
    #
    cG
    cU
    cnbgr
    co
    #
    cfn
    wcel
    #
    cU
    ve
    cv
    wcel
    ve
    cE
    crab
    #
    cfn
    wcel
    #
    @0
    @1
    @3
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @2
    @4
    wi
    #
    cU
    ve
    vf
    cE
    cG
    cV
    nbusgrf1o.v
    nbusgrf1o.e
    nbusgrf1o
    #
    @6
    @8
    vf
    @6
    @1
    @3
    @5
    wfo
    #
    @8
    @1
    @3
    @5
    f1ofo
    @2
    @10
    @4
    @1
    @3
    @5
    fofi
    expcom
    syl
    exlimiv
    syl
    @0
    @7
    @4
    @2
    wi
    #
    @9
    @6
    @11
    vf
    @6
    @1
    @3
    @5
    wf1
    #
    @11
    @1
    @3
    @5
    f1of1
    @4
    @12
    @2
    @1
    @3
    @5
    f1fi
    expcom
    syl
    exlimiv
    syl
    impbid
end
