include "weq.mm"
include "wal.mm"
include "wi.mm"
include "aevlem.mm"
include "axc16.mm"
include "syl.mm"

theorem bj-axc16g16
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t

  disjoint x y
  disjoint t z
  assert |- ( A. x x = y -> ( ph -> A. z ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vt
    weq
    vz
    wal
    wph
    wph
    vz
    wal
    wi
    vx
    vy
    vz
    vt
    aevlem
    wph
    vz
    vt
    axc16
    syl
end
