include "copab.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "nfopab1.mm"
include "nfopab2.mm"
include "dfdmf.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "opabid.mm"
include "bitri.mm"
include "exbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dmopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- dom { <. x , y >. | ph } = { x | E. y ph }

  proof
    wph
    vx
    vy
    copab
    #
    cdm
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vy
    wex
    #
    vx
    cab
    wph
    vy
    wex
    #
    vx
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
    dfdmf
    @4
    @5
    vx
    @3
    wph
    vy
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
