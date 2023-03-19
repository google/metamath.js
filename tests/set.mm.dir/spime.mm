include "wex.mm"
include "wi.mm"
include "wtru.mm"
include "wnf.mm"
include "a1i.mm"
include "spimed.mm"
include "trud.mm"

theorem spime
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume spime.1: |- F/ x ph
  assume spime.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( ph -> E. x ps )

  proof
    wph
    wps
    vx
    wex
    wi
    wph
    wps
    wtru
    vx
    vy
    wph
    vx
    wnf
    wtru
    spime.1
    a1i
    spime.2
    spimed
    trud
end
