include "wsb.mm"
include "sbf.mm"
include "nfv.mm"
include "wb.mm"
include "cdeqri.mm"
include "sbie.mm"
include "bitr3i.mm"

theorem nfcdeq
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfcdeq.1: |- F/ x ph
  assume nfcdeq.2: |- CondEq ( x = y -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  assert |- ( ph <-> ps )

  proof
    wph
    wph
    vx
    vy
    wsb
    wps
    wph
    vx
    vy
    nfcdeq.1
    sbf
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    wph
    wps
    wb
    vx
    vy
    nfcdeq.2
    cdeqri
    sbie
    bitr3i
end
