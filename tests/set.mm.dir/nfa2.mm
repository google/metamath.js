include "wal.mm"
include "alcom.mm"
include "nfa1.mm"
include "nfxfr.mm"

theorem nfa2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- F/ x A. y A. x ph

  proof
    wph
    vx
    wal
    vy
    wal
    wph
    vy
    wal
    #
    vx
    wal
    vx
    wph
    vy
    vx
    alcom
    @0
    vx
    nfa1
    nfxfr
end
