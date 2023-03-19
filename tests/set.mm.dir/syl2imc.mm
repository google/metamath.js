include "syl2im.mm"
include "com12.mm"

theorem syl2imc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2im.1: |- ( ph -> ps )
  assume syl2im.2: |- ( ch -> th )
  assume syl2im.3: |- ( ps -> ( th -> ta ) )


  assert |- ( ch -> ( ph -> ta ) )

  proof
    wph
    wch
    wta
    wph
    wps
    wch
    wth
    wta
    syl2im.1
    syl2im.2
    syl2im.3
    syl2im
    com12
end
