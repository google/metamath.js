include "wi.mm"
include "syl.mm"
include "com12.mm"

theorem syl11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl11.1: |- ( ph -> ( ps -> ch ) )
  assume syl11.2: |- ( th -> ph )


  assert |- ( ps -> ( th -> ch ) )

  proof
    wth
    wps
    wch
    wth
    wph
    wps
    wch
    wi
    syl11.2
    syl11.1
    syl
    com12
end
