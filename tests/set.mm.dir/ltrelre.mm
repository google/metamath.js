include "cltrr.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c0r.mm"
include "cop.mm"
include "wceq.mm"
include "cltr.mm"
include "wbr.mm"
include "wex.mm"
include "copab.mm"
include "cxp.mm"
include "df-lt.mm"
include "opabssxp.mm"
include "eqsstri.mm"

theorem ltrelre
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- <RR C_ ( RR X. RR )

  proof
    cltrr
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @0
    vz
    cv
    #
    c0r
    cop
    wceq
    @1
    vw
    cv
    #
    c0r
    cop
    wceq
    wa
    @2
    @3
    cltr
    wbr
    wa
    vw
    wex
    vz
    wex
    #
    wa
    vx
    vy
    copab
    cr
    cr
    cxp
    vx
    vy
    vz
    vw
    df-lt
    @4
    vx
    vy
    cr
    cr
    opabssxp
    eqsstri
end
