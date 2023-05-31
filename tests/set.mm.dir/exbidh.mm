include "wal.mm"
include "wex.mm"
include "wb.mm"
include "alexbii.mm"
include "syl.mm"

theorem exbidh
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume exbidh.1: |- ( ph -> A. x ph )
  assume exbidh.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E. x ps <-> E. x ch ) )

  proof
    wph
    wph
    vx
    wal
    wps
    vx
    wex
    wch
    vx
    wex
    wb
    exbidh.1
    wph
    wps
    wch
    vx
    exbidh.2
    alexbii
    syl
end
