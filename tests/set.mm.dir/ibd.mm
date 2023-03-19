include "wb.mm"
include "biimp.mm"
include "syli.mm"

theorem ibd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ibd.1: |- ( ph -> ( ps -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wps
    wph
    wps
    wch
    wb
    wch
    ibd.1
    wps
    wch
    biimp
    syli
end
