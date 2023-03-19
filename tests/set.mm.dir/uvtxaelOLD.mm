include "wcel.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "uvtxavalOLD.mm"
include "eleq2d.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oveq2.mm"
include "raleqbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem uvtxaelOLD
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume uvtxel.v: |- V = ( Vtx ` G )

  disjoint G n
  disjoint N n
  disjoint V n
  disjoint G v
  disjoint n v
  disjoint N v
  disjoint V v
  assert |- ( G e. W -> ( N e. ( UnivVtx ` G ) <-> ( N e. V /\ A. n e. ( V \ { N } ) n e. ( G NeighbVtx N ) ) ) )

  proof
    cG
    cW
    wcel
    #
    cN
    cG
    cuvtx
    cfv
    #
    wcel
    cN
    vn
    cv
    #
    cG
    vv
    cv
    #
    cnbgr
    co
    #
    wcel
    #
    vn
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
    cG
    cN
    cnbgr
    co
    #
    wcel
    #
    vn
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
    vv
    vn
    cG
    cV
    cW
    uvtxel.v
    uvtxavalOLD
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
    vn
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
    @2
    @3
    cN
    cG
    cnbgr
    oveq2
    eleq2d
    raleqbidv
    elrab
    syl6bb
end
