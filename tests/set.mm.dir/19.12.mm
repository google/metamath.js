include "wal.mm"
include "wex.mm"
include "nfa1.mm"
include "nfex.mm"
include "sp.mm"
include "eximi.mm"
include "alrimi.mm"

theorem 19.12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x A. y ph -> A. y E. x ph )

  proof
    wph
    vy
    wal
    #
    vx
    wex
    wph
    vx
    wex
    vy
    @0
    vy
    vx
    wph
    vy
    nfa1
    nfex
    @0
    wph
    vx
    wph
    vy
    sp
    eximi
    alrimi
end
