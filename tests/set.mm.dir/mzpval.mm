include "cvv.mm"
include "wcel.mm"
include "cmzpcl.mm"
include "cfv.mm"
include "cint.mm"
include "cmzp.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "mzpcln0.mm"
include "intex.mm"
include "sylib.mm"
include "cv.mm"
include "fveq2.mm"
include "inteqd.mm"
include "df-mzp.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem mzpval
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a


  assert |- ( V e. _V -> ( mzPoly ` V ) = |^| ( mzPolyCld ` V ) )

  proof
    cV
    cvv
    wcel
    #
    cV
    cmzpcl
    cfv
    #
    cint
    #
    cvv
    wcel
    #
    cV
    cmzp
    cfv
    @2
    wceq
    @0
    @1
    c0
    wne
    @3
    cV
    mzpcln0
    @1
    intex
    sylib
    vv
    cV
    vv
    cv
    #
    cmzpcl
    cfv
    #
    cint
    @2
    cvv
    cvv
    cmzp
    @4
    cV
    wceq
    @5
    @1
    @4
    cV
    cmzpcl
    fveq2
    inteqd
    vv
    df-mzp
    fvmptg
    mpdan
end
