include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "cuvtx.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-uvtx.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "difeq1d.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem uvtxavalOLD
  let vv: setvar v
  let vn: setvar n
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume uvtxval.v: |- V = ( Vtx ` G )

  disjoint G n
  disjoint G v
  disjoint n v
  disjoint V n
  disjoint V v
  disjoint G g
  disjoint g n
  disjoint g v
  disjoint V g
  disjoint W g
  assert |- ( G e. W -> ( UnivVtx ` G ) = { v e. V | A. n e. ( V \ { v } ) n e. ( G NeighbVtx v ) } )

  proof
    cG
    cW
    wcel
    #
    vg
    cG
    vn
    cv
    #
    vg
    cv
    #
    vv
    cv
    #
    cnbgr
    co
    #
    wcel
    #
    vn
    @2
    cvtx
    cfv
    #
    @3
    csn
    #
    cdif
    #
    wral
    #
    vv
    @6
    crab
    #
    @1
    cG
    @3
    cnbgr
    co
    #
    wcel
    #
    vn
    cV
    @7
    cdif
    #
    wral
    #
    vv
    cV
    crab
    #
    cvv
    cuvtx
    cvv
    cuvtx
    vg
    cvv
    @10
    cmpt
    wceq
    @0
    vv
    vg
    vn
    df-uvtx
    a1i
    @2
    cG
    wceq
    #
    @10
    @15
    wceq
    @0
    @16
    @9
    @14
    vv
    @6
    cV
    @16
    @6
    cG
    cvtx
    cfv
    #
    cV
    @2
    cG
    cvtx
    fveq2
    uvtxval.v
    syl6eqr
    #
    @16
    @5
    @12
    vn
    @8
    @13
    @16
    @6
    cV
    @7
    @18
    difeq1d
    @16
    @4
    @11
    @1
    @2
    cG
    @3
    cnbgr
    oveq1
    eleq2d
    raleqbidv
    rabeqbidv
    adantl
    cG
    cW
    elex
    @15
    cvv
    wcel
    @0
    @14
    vv
    cV
    cV
    @17
    cvv
    uvtxval.v
    cG
    cvtx
    fvex
    eqeltri
    rabex
    a1i
    fvmptd
end
