include "cc.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmin.mm"
include "cmul.mm"
include "wa.mm"
include "crio.mm"
include "ccj.mm"
include "df-cj.mm"
include "wreu.mm"
include "cju.mm"
include "riotacl.mm"
include "syl.mm"
include "fmpti.mm"

theorem cjf
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- * : CC --> CC

  proof
    vx
    cc
    cc
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    cr
    wcel
    ci
    @0
    @1
    cmin
    co
    cmul
    co
    cr
    wcel
    wa
    #
    vy
    cc
    crio
    #
    ccj
    vx
    vy
    df-cj
    @0
    cc
    wcel
    @2
    vy
    cc
    wreu
    @3
    cc
    wcel
    vy
    @0
    cju
    @2
    vy
    cc
    riotacl
    syl
    fmpti
end
