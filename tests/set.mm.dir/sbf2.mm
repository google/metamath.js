include "wal.mm"
include "nfa1.mm"
include "sbf.mm"

theorem sbf2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] A. x ph <-> A. x ph )

  proof
    wph
    vx
    wal
    vx
    vy
    wph
    vx
    nfa1
    sbf
end
