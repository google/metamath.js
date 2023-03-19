include "wal.mm"
include "weq.mm"
include "wi.mm"
include "ax-5.mm"
include "syl5.mm"
include "ax12v2-o.mm"

theorem ax12a2-o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax12a2-o.1: |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) )

  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )

  proof
    wph
    vx
    vy
    vz
    wph
    wph
    vz
    wal
    vx
    vz
    weq
    #
    @0
    wph
    wi
    vx
    wal
    wph
    vz
    ax-5
    ax12a2-o.1
    syl5
    ax12v2-o
end
