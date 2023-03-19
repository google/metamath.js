include "weq.mm"
include "wal.mm"
include "nfa1.mm"
include "albid.mm"
include "axc11.mm"
include "axc11r.mm"
include "impbid.mm"
include "bitrd.mm"

theorem dral1
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
    #
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
    @1
    wph
    wps
    vx
    @0
    vx
    nfa1
    dral1.1
    albid
    @1
    @2
    @3
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
