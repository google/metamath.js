include "wi.mm"
include "retbwax2.mm"
include "merco1lem7.mm"
include "ax-mp.mm"

theorem retbwax3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ph ) -> ph )

  proof
    wph
    wph
    wph
    wi
    wi
    #
    wph
    wps
    wi
    wph
    wi
    wph
    wi
    wph
    wph
    retbwax2
    @0
    wph
    wps
    merco1lem7
    ax-mp
end
