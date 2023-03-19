include "wal.mm"
include "nfa1.mm"
include "nfim.mm"

theorem nfia1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- F/ x ( A. x ph -> A. x ps )

  proof
    wph
    vx
    wal
    wps
    vx
    wal
    vx
    wph
    vx
    nfa1
    wps
    vx
    nfa1
    nfim
end
