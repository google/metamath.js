include "wex.mm"
include "wi.mm"
include "wtru.mm"
include "wnf.mm"
include "a1i.mm"
include "bj-spimedv.mm"
include "trud.mm"

theorem bj-spimev
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-spimev.1: |- F/ x ph
  assume bj-spimev.2: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
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
    bj-spimev.1
    a1i
    bj-spimev.2
    bj-spimedv
    trud
end
