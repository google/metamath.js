include "wal.mm"
include "sp.mm"
include "sps.mm"

theorem 2sp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ph -> ph )

  proof
    wph
    vy
    wal
    wph
    vx
    wph
    vy
    sp
    sps
end
