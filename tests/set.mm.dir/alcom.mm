include "wal.mm"
include "ax-11.mm"
include "impbii.mm"

theorem alcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ph <-> A. y A. x ph )

  proof
    wph
    vy
    wal
    vx
    wal
    wph
    vx
    wal
    vy
    wal
    wph
    vx
    vy
    ax-11
    wph
    vy
    vx
    ax-11
    impbii
end
