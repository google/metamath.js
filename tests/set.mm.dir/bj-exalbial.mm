include "wal.mm"
include "nfa1.mm"
include "19.9.mm"

theorem bj-exalbial
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x A. x ph <-> A. x ph )

  proof
    wph
    vx
    wal
    vx
    wph
    vx
    nfa1
    19.9
end
