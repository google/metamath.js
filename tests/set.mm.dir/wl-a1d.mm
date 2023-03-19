include "wi.mm"
include "wl-ax1.mm"
include "wl-syl.mm"

theorem wl-a1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-a1d.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wph
    wps
    wch
    wps
    wi
    wl-a1d.1
    wps
    wch
    wl-ax1
    wl-syl
end
