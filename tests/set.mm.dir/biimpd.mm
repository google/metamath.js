include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "syl.mm"

theorem biimpd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume biimpd.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wch
    wb
    wps
    wch
    wi
    biimpd.1
    wps
    wch
    biimp
    syl
end
