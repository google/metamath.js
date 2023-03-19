include "cab.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "nfab1.mm"
include "n0f.mm"
include "abid.mm"
include "exbii.mm"
include "bitri.mm"

theorem abn0
  let wph: wff ph
  let vx: setvar x


  assert |- ( { x | ph } =/= (/) <-> E. x ph )

  proof
    wph
    vx
    cab
    #
    c0
    wne
    vx
    cv
    @0
    wcel
    #
    vx
    wex
    wph
    vx
    wex
    vx
    @0
    wph
    vx
    nfab1
    n0f
    @1
    wph
    vx
    wph
    vx
    abid
    exbii
    bitri
end
