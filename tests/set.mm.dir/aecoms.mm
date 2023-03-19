include "weq.mm"
include "wal.mm"
include "aecom.mm"
include "sylbi.mm"

theorem aecoms
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
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
