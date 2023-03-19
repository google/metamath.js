include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "ax-1.mm"
include "alrimih.mm"
include "2a1i.mm"

theorem ax12f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume ax12f.1: |- ( ph -> A. x ph )


  assert |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )

  proof
    wph
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    wi
    @0
    vx
    wal
    wn
    @0
    wph
    @1
    vx
    ax12f.1
    wph
    @0
    ax-1
    alrimih
    2a1i
end
