include "wn.mm"
include "wal.mm"
include "wex.mm"
include "weq.mm"
include "notbid.mm"
include "cbvalvw.mm"
include "notbii.mm"
include "df-ex.mm"
include "3bitr4i.mm"

theorem cbvexvw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvalvw.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ph y
  assert |- ( E. x ph <-> E. y ps )

  proof
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
    @1
    @3
    @0
    @2
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    cbvalvw.1
    notbid
    cbvalvw
    notbii
    wph
    vx
    df-ex
    wps
    vy
    df-ex
    3bitr4i
end
