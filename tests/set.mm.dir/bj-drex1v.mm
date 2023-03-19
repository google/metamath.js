include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "notbid.mm"
include "bj-dral1v.mm"
include "df-ex.mm"
include "3bitr4g.mm"

theorem bj-drex1v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-drex1v.1: |- ( A. x x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( A. x x = y -> ( E. x ph <-> E. y ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wph
    wn
    #
    vx
    wal
    #
    wn
    wps
    wn
    #
    vy
    wal
    #
    wn
    wph
    vx
    wex
    wps
    vy
    wex
    @0
    @2
    @4
    @1
    @3
    vx
    vy
    @0
    wph
    wps
    bj-drex1v.1
    notbid
    bj-dral1v
    notbid
    wph
    vx
    df-ex
    wps
    vy
    df-ex
    3bitr4g
end
