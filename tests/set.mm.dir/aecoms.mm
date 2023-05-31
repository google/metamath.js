include "weq.mm"
include "wal.mm"
include "aecom.mm"
include "sylbi.mm"

theorem aecoms
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assume aecoms.1: |- ( A. x x = y -> ph )


  assert |- ( A. y y = x -> ph )

  proof
    vy
    vx
    weq
    vy
    wal
    vx
    vy
    weq
    vx
    wal
    wph
    vy
    vx
    aecom
    aecoms.1
    sylbi
end
