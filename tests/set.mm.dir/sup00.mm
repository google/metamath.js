include "c0.mm"
include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "cuni.mm"
include "df-sup.mm"
include "rab0.mm"
include "unieqi.mm"
include "uni0.mm"
include "3eqtri.mm"

theorem sup00
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- sup ( B , (/) , R ) = (/)

  proof
    cB
    c0
    cR
    csup
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    @1
    @0
    cR
    wbr
    @1
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    wi
    vy
    c0
    wral
    wa
    #
    vx
    c0
    crab
    #
    cuni
    c0
    cuni
    c0
    vx
    vy
    vz
    cB
    c0
    cR
    df-sup
    @3
    c0
    @2
    vx
    rab0
    unieqi
    uni0
    3eqtri
end
