include "wb.mm"
include "wal.mm"
include "cab.mm"
include "wceq.mm"
include "alrimi.mm"
include "bj-abbi.mm"
include "sylib.mm"

theorem bj-abbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-abbid.1: |- F/ x ph
  assume bj-abbid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> { x | ps } = { x | ch } )

  proof
    wph
    wps
    wch
    wb
    #
    vx
    wal
    wps
    vx
    cab
    wch
    vx
    cab
    wceq
    wph
    @0
    vx
    bj-abbid.1
    bj-abbid.2
    alrimi
    wps
    wch
    vx
    bj-abbi
    sylib
end
