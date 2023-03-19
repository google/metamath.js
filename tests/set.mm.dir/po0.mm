include "c0.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "ral0.mm"
include "df-po.mm"
include "mpbir.mm"

theorem po0
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- R Po (/)

  proof
    c0
    cR
    wpo
    vx
    cv
    #
    @0
    cR
    wbr
    wn
    @0
    vy
    cv
    #
    cR
    wbr
    @1
    vz
    cv
    #
    cR
    wbr
    wa
    @0
    @2
    cR
    wbr
    wi
    wa
    vz
    c0
    wral
    vy
    c0
    wral
    #
    vx
    c0
    wral
    @3
    vx
    ral0
    vx
    vy
    vz
    c0
    cR
    df-po
    mpbir
end
