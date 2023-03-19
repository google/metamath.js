include "wb.mm"
include "wal.mm"
include "cab.mm"
include "wceq.mm"
include "alrimi.mm"
include "abbi.mm"
include "sylib.mm"

theorem abbid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume abbid.1: |- F/ x ph
  assume abbid.2: |- ( ph -> ( ps <-> ch ) )


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
    abbid.1
    abbid.2
    alrimi
    wps
    wch
    vx
    abbi
    sylib
end
