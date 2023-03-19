include "wal.mm"
include "wb.mm"
include "weq.mm"
include "biidd.mm"
include "dral1.mm"
include "aecoms.mm"

theorem wl-ax11-lem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> ( A. y A. x ph <-> A. x A. y ph ) )

  proof
    wph
    vx
    wal
    #
    vy
    wal
    wph
    vy
    wal
    #
    vx
    wal
    wb
    vy
    vx
    @0
    @1
    vy
    vx
    @0
    @1
    wb
    vx
    vy
    wph
    wph
    vx
    vy
    vx
    vy
    weq
    vx
    wal
    wph
    biidd
    dral1
    aecoms
    dral1
    aecoms
end
