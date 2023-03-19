include "wal.mm"
include "ax-5.mm"
include "hbal.mm"
include "nf5i.mm"

theorem wl-nfalv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph x
  assert |- F/ x A. y ph

  proof
    wph
    vy
    wal
    vx
    wph
    vx
    vy
    wph
    vx
    ax-5
    hbal
    nf5i
end
