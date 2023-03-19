include "weq.mm"
include "ax6e.mm"
include "exlimii.mm"

theorem exlimiieq1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume exlimiieq1.1: |- F/ x ph
  assume exlimiieq1.2: |- ( x = y -> ph )


  assert |- ph

  proof
    vx
    vy
    weq
    wph
    vx
    exlimiieq1.1
    exlimiieq1.2
    vx
    vy
    ax6e
    exlimii
end
