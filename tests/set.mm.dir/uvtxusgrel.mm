include "cusgr.mm"
include "wcel.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "uvtxusgr.mm"
include "eleq2d.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem uvtxusgrel
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  assume uvtxnbgr.v: |- V = ( Vtx ` G )
  assume uvtxusgr.e: |- E = ( Edg ` G )

  disjoint G k
  disjoint V k
  disjoint N k
  disjoint G n
  disjoint N n
  disjoint V n
  disjoint k n
  disjoint V v
  disjoint k v
  disjoint E v
  disjoint G v
  disjoint N v
  assert |- ( G e. USGraph -> ( N e. ( UnivVtx ` G ) <-> ( N e. V /\ A. k e. ( V \ { N } ) { k , N } e. E ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cN
    cG
    cuvtx
    cfv
    #
    wcel
    cN
    vk
    cv
    #
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vk
    cV
    @3
    csn
    #
    cdif
    #
    wral
    #
    vv
    cV
    crab
    #
    wcel
    cN
    cV
    wcel
    @2
    cN
    cpr
    #
    cE
    wcel
    #
    vk
    cV
    cN
    csn
    #
    cdif
    #
    wral
    #
    wa
    @0
    @1
    @9
    cN
    vk
    vv
    cE
    cG
    cV
    uvtxnbgr.v
    uvtxusgr.e
    uvtxusgr
    eleq2d
    @8
    @14
    vv
    cN
    cV
    @3
    cN
    wceq
    #
    @5
    @11
    vk
    @7
    @13
    @15
    @6
    @12
    cV
    @3
    cN
    sneq
    difeq2d
    @15
    @4
    @10
    cE
    @3
    cN
    @2
    preq2
    eleq1d
    raleqbidv
    elrab
    syl6bb
end
