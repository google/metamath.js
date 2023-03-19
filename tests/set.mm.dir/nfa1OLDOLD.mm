include "wal.mm"
include "hba1.mm"
include "nfiOLD.mm"

theorem nfa1OLDOLD
  let wph: wff ph
  let vx: setvar x


  assert |- nfOLD x A. x ph

  proof
    wph
    vx
    wal
    vx
    wph
    vx
    hba1
    nfiOLD
end
