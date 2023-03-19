include "cvv.mm"
include "cxp.mm"
include "wrex.mm"
include "wex.mm"
include "rexxp.mm"
include "rexv.mm"
include "exbii.mm"
include "3bitri.mm"

theorem exopxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume exopxfr.1: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  disjoint x y
  disjoint x z
  assert |- ( E. x e. ( _V X. _V ) ph <-> E. y E. z ps )

  proof
    wph
    vx
    cvv
    cvv
    cxp
    wrex
    wps
    vz
    cvv
    wrex
    #
    vy
    cvv
    wrex
    @0
    vy
    wex
    wps
    vz
    wex
    #
    vy
    wex
    wph
    wps
    vx
    vy
    vz
    cvv
    cvv
    exopxfr.1
    rexxp
    @0
    vy
    rexv
    @0
    @1
    vy
    wps
    vz
    rexv
    exbii
    3bitri
end
