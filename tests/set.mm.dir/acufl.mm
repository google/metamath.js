include "wac.mm"
include "cufl.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "vex.mm"
include "pwex.mm"
include "wceq.mm"
include "dfac10.mm"
include "biimpi.mm"
include "syl5eleqr.mm"
include "numufl.mm"
include "syl.mm"
include "a1i.mm"
include "2thd.mm"
include "eqrdv.mm"

theorem acufl
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vu: setvar u
  let vx: setvar x
  let cX: class X
  let cY: class Y


  assert |- ( CHOICE -> UFL = _V )

  proof
    wac
    vx
    cufl
    cvv
    wac
    vx
    cv
    #
    cufl
    wcel
    #
    @0
    cvv
    wcel
    #
    wac
    @0
    cpw
    #
    cpw
    #
    ccrd
    cdm
    #
    wcel
    @1
    wac
    @4
    cvv
    @5
    @3
    @0
    vx
    vex
    #
    pwex
    pwex
    wac
    @5
    cvv
    wceq
    dfac10
    biimpi
    syl5eleqr
    @0
    numufl
    syl
    @2
    wac
    @6
    a1i
    2thd
    eqrdv
end
