include "wb.mm"
include "wi.mm"
include "pm5.74.mm"
include "mpbir.mm"

theorem pm5.74ri
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume pm5.74ri.1: |- ( ( ph -> ps ) <-> ( ph -> ch ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    wb
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wb
    pm5.74ri.1
    wph
    wps
    wch
    pm5.74
    mpbir
end
