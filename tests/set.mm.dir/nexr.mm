include "wex.mm"
include "19.8a.mm"
include "mto.mm"

theorem nexr
  let wph: wff ph
  let vx: setvar x
  assume nexr.1: |- -. E. x ph


  assert |- -. ph

  proof
    wph
    wph
    vx
    wex
    nexr.1
    wph
    vx
    19.8a
    mto
end
