include "orcd.mm"
include "orcomd.mm"

theorem olcd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume orcd.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch \/ ps ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    orcd.1
    orcd
    orcomd
end
