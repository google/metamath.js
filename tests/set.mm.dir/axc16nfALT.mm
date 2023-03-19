include "weq.mm"
include "wal.mm"
include "nfae.mm"
include "axc16g.mm"
include "nf5d.mm"

theorem axc16nfALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( A. x x = y -> F/ z ph )

  proof
    vx
    vy
    weq
    vx
    wal
    wph
    vz
    vx
    vy
    vz
    nfae
    wph
    vx
    vy
    vz
    axc16g
    nf5d
end
