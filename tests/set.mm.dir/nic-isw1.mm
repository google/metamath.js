include "wnan.mm"
include "nic-swap.mm"
include "nic-mp.mm"

theorem nic-isw1
  let wph: wff ph
  let wth: wff th
  assume nic-isw1.1: |- ( th -/\ ph )


  assert |- ( ph -/\ th )

  proof
    wth
    wph
    wnan
    wph
    wth
    wnan
    #
    @0
    nic-isw1.1
    wph
    wth
    nic-swap
    nic-mp
end
