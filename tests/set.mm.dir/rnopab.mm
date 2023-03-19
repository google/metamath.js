include "copab.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "nfopab1.mm"
include "nfopab2.mm"
include "dfrnf.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "opabid.mm"
include "bitri.mm"
include "exbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem rnopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ran { <. x , y >. | ph } = { y | E. x ph }

  proof
    wph
    vx
    vy
    copab
    #
    crn
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vx
    wex
    #
    vy
    cab
    wph
    vx
    wex
    #
    vy
    cab
    vx
    vy
    @0
    wph
    vx
    vy
    nfopab1
    wph
    vx
    vy
    nfopab2
    dfrnf
    @4
    @5
    vy
    @3
    wph
    vx
    @3
    @1
    @2
    cop
    @0
    wcel
    wph
    @1
    @2
    @0
    df-br
    wph
    vx
    vy
    opabid
    bitri
    exbii
    abbii
    eqtri
end
