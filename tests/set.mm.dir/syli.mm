include "com12.mm"
include "sylcom.mm"

theorem syli
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syli.1: |- ( ps -> ( ph -> ch ) )
  assume syli.2: |- ( ch -> ( ph -> th ) )


  assert |- ( ps -> ( ph -> th ) )

  proof
    wps
    wph
    wch
    wth
    syli.1
    wch
    wph
    wth
    syli.2
    com12
    sylcom
end
