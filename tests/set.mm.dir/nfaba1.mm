include "wal.mm"
include "nfa1.mm"
include "nfab.mm"

theorem nfaba1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- F/_ x { y | A. x ph }

  proof
    wph
    vx
    wal
    vx
    vy
    wph
    vx
    nfa1
    nfab
end
