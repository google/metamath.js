include "wal.mm"
include "nfa1.mm"
include "19.23.mm"

theorem bj-biexal1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ps ) <-> ( E. x ph -> A. x ps ) )

  proof
    wph
    wps
    vx
    wal
    vx
    wps
    vx
    nfa1
    19.23
end
