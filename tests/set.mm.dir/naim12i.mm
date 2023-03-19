include "naim1i.mm"
include "naim2i.mm"

theorem naim12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume naim12i.1: |- ( ph -> ps )
  assume naim12i.2: |- ( ch -> th )
  assume naim12i.3: |- ( ps -/\ th )


  assert |- ( ph -/\ ch )

  proof
    wch
    wth
    wph
    naim12i.2
    wph
    wps
    wth
    naim12i.1
    naim12i.3
    naim1i
    naim2i
end
