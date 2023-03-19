include "c0.mm"
include "wceq.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "uvtxval.mm"
include "rabeq.mm"
include "rab0.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem uvtx0
  let cG: class G
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  let cN: class N
  assume uvtxel.v: |- V = ( Vtx ` G )


  assert |- ( V = (/) -> ( UnivVtx ` G ) = (/) )

  proof
    cV
    c0
    wceq
    #
    cG
    cuvtx
    cfv
    vn
    cv
    cG
    vv
    cv
    #
    cnbgr
    co
    wcel
    vn
    cV
    @1
    csn
    cdif
    wral
    #
    vv
    cV
    crab
    #
    c0
    vv
    vn
    cG
    cV
    uvtxel.v
    uvtxval
    @0
    @3
    @2
    vv
    c0
    crab
    c0
    @2
    vv
    cV
    c0
    rabeq
    @2
    vv
    rab0
    syl6eq
    syl5eq
end
