include "wi.mm"
include "imim1i.mm"
include "syl.mm"

theorem wl-syls2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-syls2.1: |- ( ph -> ps )
  assume wl-syls2.2: |- ( ( ph -> ch ) -> th )


  assert |- ( ( ps -> ch ) -> th )

  proof
    wps
    wch
    wi
    wph
    wch
    wi
    wth
    wph
    wps
    wch
    wl-syls2.1
    imim1i
    wl-syls2.2
    syl
end
