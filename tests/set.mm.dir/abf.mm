include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "ab0.mm"
include "mpgbir.mm"

theorem abf
  let wph: wff ph
  let vx: setvar x
  assume abf.1: |- -. ph


  assert |- { x | ph } = (/)

  proof
    wph
    vx
    cab
    c0
    wceq
    wph
    wn
    vx
    wph
    vx
    ab0
    abf.1
    mpgbir
end
