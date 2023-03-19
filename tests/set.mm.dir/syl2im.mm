include "wi.mm"
include "syl5.mm"
include "syl.mm"

theorem syl2im
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
