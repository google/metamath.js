include "weq.mm"
include "wal.mm"
include "nfa1.mm"
include "albid.mm"
include "bj-axc11v.mm"
include "axc11r.mm"
include "impbid.mm"
include "bitrd.mm"

theorem bj-dral1v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-dral1v.1: |- ( A. x x = y -> ( ph <-> ps ) )

  disjoint x y
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
    bj-dral1v.1
    albid
    @1
    @2
    @3
    wps
    vx
    vy
    bj-axc11v
    wps
    vy
    vx
    axc11r
    impbid
    bitrd
end
