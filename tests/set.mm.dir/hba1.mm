include "wal.mm"
include "nfa1.mm"
include "nf5ri.mm"

theorem hba1
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ph -> A. x A. x ph )

  proof
    wph
    vx
    wal
    vx
    wph
    vx
    nfa1
    nf5ri
end
