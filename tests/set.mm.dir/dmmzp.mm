include "cmzp.mm"
include "cdm.mm"
include "cvv.mm"
include "cv.mm"
include "cmzpcl.mm"
include "cfv.mm"
include "cint.mm"
include "cmpt.mm"
include "df-mzp.mm"
include "dmeqi.mm"
include "wcel.mm"
include "wceq.mm"
include "dmmptg.mm"
include "c0.mm"
include "wne.mm"
include "mzpcln0.mm"
include "intex.mm"
include "sylib.mm"
include "mprg.mm"
include "eqtri.mm"

theorem dmmzp
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a


  assert |- dom mzPoly = _V

  proof
    cmzp
    cdm
    vv
    cvv
    vv
    cv
    #
    cmzpcl
    cfv
    #
    cint
    #
    cmpt
    #
    cdm
    #
    cvv
    cmzp
    @3
    vv
    df-mzp
    dmeqi
    @2
    cvv
    wcel
    #
    @4
    cvv
    wceq
    vv
    cvv
    vv
    cvv
    @2
    cvv
    dmmptg
    @0
    cvv
    wcel
    @1
    c0
    wne
    @5
    @0
    mzpcln0
    @1
    intex
    sylib
    mprg
    eqtri
end
