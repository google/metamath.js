include "wal.mm"
include "nfa1.mm"
include "19.3.mm"

theorem bj-alalbial
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x A. x ph <-> A. x ph )

  proof
    wph
    vx
    wal
    vx
    wph
    vx
    nfa1
    19.3
end
