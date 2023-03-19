include "wi.mm"
include "a2i.mm"
include "syl.mm"

theorem sylcom
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume sylcom.1: |- ( ph -> ( ps -> ch ) )
  assume sylcom.2: |- ( ps -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wth
    wi
    sylcom.1
    wps
    wch
    wth
    sylcom.2
    a2i
    syl
end
