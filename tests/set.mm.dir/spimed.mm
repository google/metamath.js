include "wal.mm"
include "wex.mm"
include "nf5rd.mm"
include "weq.mm"
include "wi.mm"
include "ax6e.mm"
include "eximii.mm"
include "19.35i.mm"
include "syl6.mm"

theorem spimed
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume spimed.1: |- ( ch -> F/ x ph )
  assume spimed.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( ch -> ( ph -> E. x ps ) )

  proof
    wch
    wph
    wph
    vx
    wal
    wps
    vx
    wex
    wch
    wph
    vx
    spimed.1
    nf5rd
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
    ax6e
    spimed.2
    eximii
    19.35i
    syl6
end
