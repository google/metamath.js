include "orcd.mm"
include "orcomd.mm"

theorem olcd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
