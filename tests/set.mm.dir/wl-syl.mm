include "wi.mm"
include "wl-imim1i.mm"
include "ax-mp.mm"

theorem wl-syl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-syl.1: |- ( ph -> ps )
  assume wl-syl.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wps
    wch
    wi
    wph
    wch
    wi
    wl-syl.2
    wph
    wps
    wch
    wl-syl.1
    wl-imim1i
    ax-mp
end
