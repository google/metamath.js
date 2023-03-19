include "cvv.mm"
include "weq.mm"
include "cab.mm"
include "df-v.mm"
include "equid.mm"
include "2th.mm"
include "abbii.mm"
include "eqtri.mm"

theorem foo3
  let wph: wff ph
  let vx: setvar x
  assume foo3.1: |- ph


  assert |- _V = { x | ph }

  proof
    cvv
    vx
    vx
    weq
    #
    vx
    cab
    wph
    vx
    cab
    vx
    df-v
    @0
    wph
    vx
    @0
    wph
    vx
    equid
    foo3.1
    2th
    abbii
    eqtri
end
