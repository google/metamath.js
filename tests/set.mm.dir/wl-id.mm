include "wn.mm"
include "wi.mm"
include "ax-luk3.mm"
include "ax-luk2.mm"
include "wl-syl.mm"

theorem wl-id
  let wph: wff ph


  assert |- ( ph -> ph )

  proof
    wph
    wph
    wn
    wph
    wi
    wph
    wph
    wph
    ax-luk3
    wph
    ax-luk2
    wl-syl
end
