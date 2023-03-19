include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "uvtxval.mm"
include "elrab2.mm"

theorem uvtxel
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  let vv: setvar v
  assume uvtxel.v: |- V = ( Vtx ` G )

  disjoint G n
  disjoint N n
  disjoint V n
  disjoint G v
  disjoint n v
  disjoint N v
  disjoint V v
  assert |- ( N e. ( UnivVtx ` G ) <-> ( N e. V /\ A. n e. ( V \ { N } ) n e. ( G NeighbVtx N ) ) )

  proof
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
    @1
    csn
    #
    cdif
    #
    wral
    @0
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
    vv
    cN
    cV
    cG
    cuvtx
    cfv
    @1
    cN
    wceq
    #
    @3
    @7
    vn
    @5
    @9
    @10
    @4
    @8
    cV
    @1
    cN
    sneq
    difeq2d
    @10
    @2
    @6
    @0
    @1
    cN
    cG
    cnbgr
    oveq2
    eleq2d
    raleqbidv
    vv
    vn
    cG
    cV
    uvtxel.v
    uvtxval
    elrab2
end
