include "wal.mm"
include "hba1-o.mm"
include "nf5i.mm"

theorem nfa1-o
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
    hba1-o
    nf5i
end
