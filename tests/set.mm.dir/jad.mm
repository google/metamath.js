include "wi.mm"
include "wn.mm"
include "com12.mm"
include "ja.mm"

theorem jad
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jad.1: |- ( ph -> ( -. ps -> th ) )
  assume jad.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ( ps -> ch ) -> th ) )

  proof
    wps
    wch
    wi
    wph
    wth
    wps
    wch
    wph
    wth
    wi
    wph
    wps
    wn
    wth
    jad.1
    com12
    wph
    wch
    wth
    jad.2
    com12
    ja
    com12
end
