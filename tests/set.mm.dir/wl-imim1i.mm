include "wi.mm"
include "ax-luk1.mm"
include "ax-mp.mm"

theorem wl-imim1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-imim1i.1: |- ( ph -> ps )


  assert |- ( ( ps -> ch ) -> ( ph -> ch ) )

  proof
    wph
    wps
    wi
    wps
    wch
    wi
    wph
    wch
    wi
    wi
    wl-imim1i.1
    wph
    wps
    wch
    ax-luk1
    ax-mp
end
