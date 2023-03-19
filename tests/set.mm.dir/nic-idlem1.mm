include "wnan.mm"
include "nic-ax.mm"
include "nic-imp.mm"

theorem nic-idlem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) )

  proof
    wph
    wch
    wps
    wnan
    wnan
    wph
    wch
    wnan
    wph
    wph
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
    wth
    wph
    wps
    wch
    wph
    wta
    nic-ax
    nic-imp
end
