include "wal.mm"
include "hba1.mm"
include "nf5i.mm"

theorem nfa1OLD
  let wph: wff ph
  let vx: setvar x


  assert |- F/ x A. x ph

  proof
    wph
    vx
    wal
    vx
    wph
    vx
    hba1
    nf5i
end
