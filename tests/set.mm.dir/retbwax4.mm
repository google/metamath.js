include "wfal.mm"
include "wi.mm"
include "merco1lem1.mm"
include "ax-mp.mm"

theorem retbwax4
  let wph: wff ph


  assert |- ( F. -> ph )

  proof
    wph
    wfal
    wph
    wi
    #
    wi
    #
    @0
    wph
    wph
    merco1lem1
    @1
    wph
    merco1lem1
    ax-mp
end
