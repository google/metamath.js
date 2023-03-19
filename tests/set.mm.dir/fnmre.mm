include "cvv.mm"
include "wel.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wcel.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "cmre.mm"
include "vpwex.mm"
include "pwex.mm"
include "rabex.mm"
include "df-mre.mm"
include "fnmpti.mm"

theorem fnmre
  let cC: class C
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let cX: class X
  let cS: class S


  assert |- Moore Fn _V

  proof
    vx
    cvv
    vx
    vc
    wel
    vs
    cv
    #
    c0
    wne
    @0
    cint
    vc
    cv
    #
    wcel
    wi
    vs
    @1
    cpw
    wral
    wa
    #
    vc
    vx
    cv
    cpw
    #
    cpw
    #
    crab
    cmre
    @2
    vc
    @4
    @3
    vx
    vpwex
    pwex
    rabex
    vx
    vs
    vc
    df-mre
    fnmpti
end
