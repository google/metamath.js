include "wn.mm"
include "wi.mm"
include "ax-luk3.mm"
include "wl-ax3.mm"
include "wl-syl.mm"

theorem wl-ax1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ph ) )

  proof
    wph
    wph
    wn
    wps
    wn
    #
    wi
    wps
    wph
    wi
    wph
    @0
    ax-luk3
    wph
    wps
    wl-ax3
    wl-syl
end
