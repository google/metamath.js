include "syl6bb.mm"
include "bicomd.mm"

theorem syl6rbb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl6rbb.1: |- ( ph -> ( ps <-> ch ) )
  assume syl6rbb.2: |- ( ch <-> th )


  assert |- ( ph -> ( th <-> ps ) )

  proof
    wph
    wps
    wth
    wph
    wps
    wch
    wth
    syl6rbb.1
    syl6rbb.2
    syl6bb
    bicomd
end
