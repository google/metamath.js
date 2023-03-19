include "wi.mm"
include "ax-luk1.mm"
include "wl-com12.mm"

theorem wl-imim2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )

  proof
    wch
    wph
    wi
    wph
    wps
    wi
    wch
    wps
    wi
    wch
    wph
    wps
    ax-luk1
    wl-com12
end
