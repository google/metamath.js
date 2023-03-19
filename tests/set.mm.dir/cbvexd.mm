include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfnd.mm"
include "weq.mm"
include "wb.mm"
include "notbi.mm"
include "syl6ib.mm"
include "cbvald.mm"
include "notbid.mm"
include "df-ex.mm"
include "3bitr4g.mm"

theorem cbvexd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbvald.1: |- F/ y ph
  assume cbvald.2: |- ( ph -> F/ y ps )
  assume cbvald.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( E. x ps <-> E. y ch ) )

  proof
    wph
    wps
    wn
    #
    vx
    wal
    #
    wn
    wch
    wn
    #
    vy
    wal
    #
    wn
    wps
    vx
    wex
    wch
    vy
    wex
    wph
    @1
    @3
    wph
    @0
    @2
    vx
    vy
    cbvald.1
    wph
    wps
    vy
    cbvald.2
    nfnd
    wph
    vx
    vy
    weq
    wps
    wch
    wb
    @0
    @2
    wb
    cbvald.3
    wps
    wch
    notbi
    syl6ib
    cbvald
    notbid
    wps
    vx
    df-ex
    wch
    vy
    df-ex
    3bitr4g
end
