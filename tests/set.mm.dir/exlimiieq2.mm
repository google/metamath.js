include "weq.mm"
include "ax6er.mm"
include "exlimii.mm"

theorem exlimiieq2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume exlimiieq2.1: |- F/ y ph
  assume exlimiieq2.2: |- ( x = y -> ph )


  assert |- ph

  proof
    vx
    vy
    weq
    wph
    vy
    exlimiieq2.1
    exlimiieq2.2
    vy
    vx
    ax6er
    exlimii
end
