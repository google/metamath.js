include "cof.mm"
include "wfun.mm"
include "wcel.mm"
include "cres.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cin.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "df-of.mm"
include "mpt2fun.mm"
include "resfunexg.mm"
include "mpan.mm"

theorem ofexg
  let cA: class A
  let cR: class R
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cS: class S


  assert |- ( A e. V -> ( oF R |` A ) e. _V )

  proof
    cR
    cof
    #
    wfun
    cA
    cV
    wcel
    @0
    cA
    cres
    cvv
    wcel
    vf
    vg
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    vg
    cv
    #
    cdm
    cin
    vx
    cv
    #
    @1
    cfv
    @3
    @2
    cfv
    cR
    co
    cmpt
    @0
    vx
    cR
    vf
    vg
    df-of
    mpt2fun
    @0
    cA
    cV
    resfunexg
    mpan
end
