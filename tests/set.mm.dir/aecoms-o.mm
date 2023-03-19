include "weq.mm"
include "wal.mm"
include "aecom-o.mm"
include "syl.mm"

theorem aecoms-o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume alequcoms-o.1: |- ( A. x x = y -> ph )


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
    aecom-o
    alequcoms-o.1
    syl
end
