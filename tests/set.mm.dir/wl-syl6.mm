include "wi.mm"
include "wl-imim2i.mm"
include "wl-syl.mm"

theorem wl-syl6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-syl6.1: |- ( ph -> ( ps -> ch ) )
  assume wl-syl6.2: |- ( ch -> th )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wth
    wi
    wl-syl6.1
    wch
    wth
    wps
    wl-syl6.2
    wl-imim2i
    wl-syl
end
