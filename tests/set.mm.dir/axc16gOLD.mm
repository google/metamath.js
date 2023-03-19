include "weq.mm"
include "wal.mm"
include "aevlem.mm"
include "ax-5.mm"
include "axc11rvOLD.mm"
include "syl2im.mm"

theorem axc16gOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- ( A. x x = y -> ( ph -> A. z ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vw
    weq
    vz
    wal
    wph
    wph
    vw
    wal
    wph
    vz
    wal
    vx
    vy
    vz
    vw
    aevlem
    wph
    vw
    ax-5
    wph
    vz
    vw
    axc11rvOLD
    syl2im
end
