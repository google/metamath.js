include "wal.mm"
include "nfa1.mm"
include "nfn.mm"

theorem nfna1
  let wph: wff ph
  let vx: setvar x


  assert |- F/ x -. A. x ph

  proof
    wph
    vx
    wal
    vx
    wph
    vx
    nfa1
    nfn
end
