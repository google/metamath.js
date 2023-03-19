include "wnan.mm"
include "wn.mm"
include "wi.mm"
include "wl-dfnan2.mm"
include "pm4.8.mm"
include "bitr2i.mm"

theorem wl-nannot
  let wph: wff ph


  assert |- ( -. ph <-> ( ph -/\ ph ) )

  proof
    wph
    wph
    wnan
    wph
    wph
    wn
    #
    wi
    @0
    wph
    wph
    wl-dfnan2
    wph
    pm4.8
    bitr2i
end
