include "weq.mm"
include "wal.mm"
include "dral2.mm"
include "axc11.mm"
include "axc11r.mm"
include "impbid.mm"
include "bitrd.mm"

theorem dral1ALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume dral1.1: |- ( A. x x = y -> ( ph <-> ps ) )


  assert |- ( A. x x = y -> ( A. x ph <-> A. y ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wph
    vx
    wal
    wps
    vx
    wal
    #
    wps
    vy
    wal
    #
    wph
    wps
    vx
    vy
    vx
    dral1.1
    dral2
    @0
    @1
    @2
    wps
    vx
    vy
    axc11
    wps
    vy
    vx
    axc11r
    impbid
    bitrd
end
