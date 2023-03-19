include "wnan.mm"
include "nic-id.mm"
include "nic-ax.mm"
include "nic-mp.mm"

theorem nic-swap
  let wph: wff ph
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) )

  proof
    wph
    wph
    wph
    wnan
    wnan
    wth
    wph
    wnan
    wph
    wth
    wnan
    #
    @0
    wnan
    wnan
    wta
    wta
    wta
    wnan
    wnan
    wph
    nic-id
    wph
    wph
    wph
    wth
    wta
    nic-ax
    nic-mp
end
