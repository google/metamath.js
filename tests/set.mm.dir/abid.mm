include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "sbid.mm"
include "bitri.mm"

theorem abid
  let wph: wff ph
  let vx: setvar x


  assert |- ( x e. { x | ph } <-> ph )

  proof
    vx
    cv
    wph
    vx
    cab
    wcel
    wph
    vx
    vx
    wsb
    wph
    wph
    vx
    vx
    df-clab
    wph
    vx
    sbid
    bitri
end
