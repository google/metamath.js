include "wal.mm"
include "wex.mm"
include "weq.mm"
include "wi.mm"
include "ax6ev.mm"
include "eximii.mm"
include "19.35i.mm"
include "syl.mm"

theorem spimeh
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spimeh.1: |- ( ph -> A. x ph )
  assume spimeh.2: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  assert |- ( ph -> E. x ps )

  proof
    wph
    wph
    vx
    wal
    wps
    vx
    wex
    spimeh.1
    wph
    wps
    vx
    vx
    vy
    weq
    wph
    wps
    wi
    vx
    vx
    vy
    ax6ev
    spimeh.2
    eximii
    19.35i
    syl
end
