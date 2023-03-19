include "wi.mm"
include "ax-1.mm"
include "syl.mm"

theorem wl-jarri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-jarri.1: |- ( ( ph -> ps ) -> ch )


  assert |- ( ps -> ch )

  proof
    wps
    wph
    wps
    wi
    wch
    wps
    wph
    ax-1
    wl-jarri.1
    syl
end
