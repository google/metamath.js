include "biimpi.mm"
include "syl.mm"

theorem sylib
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume sylib.1: |- ( ph -> ps )
  assume sylib.2: |- ( ps <-> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    sylib.1
    wps
    wch
    sylib.2
    biimpi
    syl
end
