include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "sbco.mm"
include "sb6.mm"
include "bitr3i.mm"

theorem sb6a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) )

  proof
    wph
    vx
    vy
    wsb
    wph
    vy
    vx
    wsb
    #
    vx
    vy
    wsb
    vx
    vy
    weq
    @0
    wi
    vx
    wal
    wph
    vx
    vy
    sbco
    @0
    vx
    vy
    sb6
    bitr3i
end
