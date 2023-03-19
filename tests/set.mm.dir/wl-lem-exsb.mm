include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ax12v2.mm"
include "sp.mm"
include "com12.mm"
include "impbid.mm"

theorem wl-lem-exsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( x = y -> ( ph <-> A. x ( x = y -> ph ) ) )

  proof
    vx
    vy
    weq
    #
    wph
    @0
    wph
    wi
    #
    vx
    wal
    #
    wph
    vx
    vy
    ax12v2
    @2
    @0
    wph
    @1
    vx
    sp
    com12
    impbid
end
