include "wex.mm"
include "19.9h.mm"
include "mpbi.mm"

theorem bnj1131
  let wph: wff ph
  let vx: setvar x
  assume bnj1131.1: |- ( ph -> A. x ph )
  assume bnj1131.2: |- E. x ph


  assert |- ph

  proof
    wph
    vx
    wex
    wph
    bnj1131.2
    wph
    vx
    bnj1131.1
    19.9h
    mpbi
end
