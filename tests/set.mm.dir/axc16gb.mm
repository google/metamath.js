include "weq.mm"
include "wal.mm"
include "axc16g.mm"
include "sp.mm"
include "impbid1.mm"

theorem axc16gb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( A. x x = y -> ( ph <-> A. z ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wph
    wph
    vz
    wal
    wph
    vx
    vy
    vz
    axc16g
    wph
    vz
    sp
    impbid1
end
