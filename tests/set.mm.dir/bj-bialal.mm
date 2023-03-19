include "wal.mm"
include "nfa1.mm"
include "19.21.mm"

theorem bj-bialal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( A. x ph -> ps ) <-> ( A. x ph -> A. x ps ) )

  proof
    wph
    vx
    wal
    wps
    vx
    wph
    vx
    nfa1
    19.21
end
