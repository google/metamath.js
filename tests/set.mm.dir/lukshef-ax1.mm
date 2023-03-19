include "nic-ax.mm"

theorem lukshef-ax1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( th -/\ ( th -/\ th ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wth
    nic-ax
end
