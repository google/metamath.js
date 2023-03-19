include "wi.mm"
include "wl-imim1i.mm"
include "wl-syl.mm"

theorem wl-syl5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-syl5.1: |- ( ph -> ps )
  assume wl-syl5.2: |- ( ch -> ( ps -> th ) )


  assert |- ( ch -> ( ph -> th ) )

  proof
    wch
    wps
    wth
    wi
    wph
    wth
    wi
    wl-syl5.2
    wph
    wps
    wth
    wl-syl5.1
    wl-imim1i
    wl-syl
end
