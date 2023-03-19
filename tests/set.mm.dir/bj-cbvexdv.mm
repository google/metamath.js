include "wn.mm"
include "wal.mm"
include "wex.mm"
include "nfnd.mm"
include "weq.mm"
include "wb.mm"
include "notbi.mm"
include "syl6ib.mm"
include "bj-cbvaldv.mm"
include "notbid.mm"
include "df-ex.mm"
include "3bitr4g.mm"

theorem bj-cbvexdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvaldv.1: |- F/ y ph
  assume bj-cbvaldv.2: |- ( ph -> F/ y ps )
  assume bj-cbvaldv.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )

  disjoint x y
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
    bj-cbvaldv.1
    wph
    wps
    vy
    bj-cbvaldv.2
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
    bj-cbvaldv.3
    wps
    wch
    notbi
    syl6ib
    bj-cbvaldv
    notbid
    wps
    vx
    df-ex
    wch
    vy
    df-ex
    3bitr4g
end
