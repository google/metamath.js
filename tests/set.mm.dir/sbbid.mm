include "wb.mm"
include "wal.mm"
include "wsb.mm"
include "alrimi.mm"
include "spsbbi.mm"
include "syl.mm"

theorem sbbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume sbbid.1: |- F/ x ph
  assume sbbid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) )

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
    vy
    wsb
    wch
    vx
    vy
    wsb
    wb
    wph
    @0
    vx
    sbbid.1
    sbbid.2
    alrimi
    wps
    wch
    vx
    vy
    spsbbi
    syl
end
