include "wnan.mm"
include "nic-ax.mm"
include "nic-mp.mm"

theorem nic-imp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume nic-imp.1: |- ( ph -/\ ( ch -/\ ps ) )


  assert |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) )

  proof
    wph
    wch
    wps
    wnan
    wnan
    wth
    wch
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
    nic-imp.1
    wph
    wps
    wch
    wth
    wta
    nic-ax
    nic-mp
end
