include "wi.mm"
include "syl5.mm"
include "syl.mm"

theorem syl2im
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl2im.1: |- ( ph -> ps )
  assume syl2im.2: |- ( ch -> th )
  assume syl2im.3: |- ( ps -> ( th -> ta ) )


  assert |- ( ph -> ( ch -> ta ) )

  proof
    wph
    wps
    wch
    wta
    wi
    syl2im.1
    wch
    wth
    wps
    wta
    syl2im.2
    syl2im.3
    syl5
    syl
end
