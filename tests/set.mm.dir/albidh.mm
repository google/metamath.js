include "wb.mm"
include "wal.mm"
include "alrimih.mm"
include "albi.mm"
include "syl.mm"

theorem albidh
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume albidh.1: |- ( ph -> A. x ph )
  assume albidh.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x ps <-> A. x ch ) )

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
    wal
    wch
    vx
    wal
    wb
    wph
    @0
    vx
    albidh.1
    albidh.2
    alrimih
    wps
    wch
    vx
    albi
    syl
end
