include "wal.mm"
include "weq.mm"
include "wi.mm"
include "ax-5.mm"
include "ax-12.mm"
include "syl5.mm"

theorem ax12v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) )

  proof
    wph
    wph
    vy
    wal
    vx
    vy
    weq
    #
    @0
    wph
    wi
    vx
    wal
    wph
    vy
    ax-5
    wph
    vx
    vy
    ax-12
    syl5
end
