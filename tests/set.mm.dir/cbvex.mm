include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfn.mm"
include "weq.mm"
include "notbid.mm"
include "cbval.mm"
include "notbii.mm"
include "df-ex.mm"
include "3bitr4i.mm"

theorem cbvex
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume cbval.1: |- F/ y ph
  assume cbval.2: |- F/ x ps
  assume cbval.3: |- ( x = y -> ( ph <-> ps ) )


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
    wph
    vy
    cbval.1
    nfn
    wps
    vx
    cbval.2
    nfn
    vx
    vy
    weq
    wph
    wps
    cbval.3
    notbid
    cbval
    notbii
    wph
    vx
    df-ex
    wps
    vy
    df-ex
    3bitr4i
end
