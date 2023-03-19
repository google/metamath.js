include "wal.mm"
include "nfa1.mm"
include "nfal.mm"

theorem nfa2OLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- F/ x A. y A. x ph

  proof
    wph
    vx
    wal
    vx
    vy
    wph
    vx
    nfa1
    nfal
end
