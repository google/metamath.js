include "syl5bb.mm"
include "bicomd.mm"

theorem syl5rbb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5rbb.1: |- ( ph <-> ps )
  assume syl5rbb.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ch -> ( th <-> ph ) )

  proof
    wch
    wph
    wth
    wph
    wps
    wch
    wth
    syl5rbb.1
    syl5rbb.2
    syl5bb
    bicomd
end
