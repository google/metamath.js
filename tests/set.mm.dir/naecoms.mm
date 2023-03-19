include "weq.mm"
include "wal.mm"
include "aecom.mm"
include "sylnbir.mm"

theorem naecoms
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume naecoms.1: |- ( -. A. x x = y -> ph )


  assert |- ( -. A. y y = x -> ph )

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
    vx
    vy
    aecom
    naecoms.1
    sylnbir
end
