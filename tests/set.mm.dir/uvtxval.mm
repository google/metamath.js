include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cvtx.mm"
include "crab.mm"
include "df-uvtx.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "difeq1d.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "fvmptrabfv.mm"
include "eqcomi.mm"
include "rabeqi.mm"
include "eqtri.mm"

theorem uvtxval
  let vv: setvar v
  let vn: setvar n
  let cG: class G
  let cV: class V
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
  assert |- ( UnivVtx ` G ) = { v e. V | A. n e. ( V \ { v } ) n e. ( G NeighbVtx v ) }

  proof
    cG
    cuvtx
    cfv
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
    #
    vv
    cG
    cvtx
    cfv
    #
    crab
    @6
    vv
    cV
    crab
    @0
    vg
    cv
    #
    @1
    cnbgr
    co
    #
    wcel
    #
    vn
    @8
    cvtx
    cfv
    #
    @4
    cdif
    #
    wral
    @6
    vg
    vv
    cuvtx
    cvtx
    cG
    vv
    vg
    vn
    df-uvtx
    @8
    cG
    wceq
    #
    @10
    @3
    vn
    @12
    @5
    @13
    @11
    cV
    @4
    @13
    @11
    @7
    cV
    @8
    cG
    cvtx
    fveq2
    uvtxval.v
    syl6eqr
    difeq1d
    @13
    @9
    @2
    @0
    @8
    cG
    @1
    cnbgr
    oveq1
    eleq2d
    raleqbidv
    fvmptrabfv
    @6
    vv
    @7
    cV
    cV
    @7
    uvtxval.v
    eqcomi
    rabeqi
    eqtri
end
