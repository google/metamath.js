include "wn.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "bj-ab0.mm"
include "mpg.mm"

theorem bj-abf
  let wph: wff ph
  let vx: setvar x
  assume bj-abf.1: |- -. ph


  assert |- { x | ph } = (/)

  proof
    wph
    wn
    wph
    vx
    cab
    c0
    wceq
    vx
    wph
    vx
    bj-ab0
    bj-abf.1
    mpg
end
