include "nabi1i.mm"
include "nabi2i.mm"

theorem nabi12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nabi12i.1: |- ( ph <-> ps )
  assume nabi12i.2: |- ( ch <-> th )
  assume nabi12i.3: |- ( ps -/\ th )


  assert |- ( ph -/\ ch )

  proof
    wch
    wth
    wph
    nabi12i.2
    wph
    wps
    wth
    nabi12i.1
    nabi12i.3
    nabi1i
    nabi2i
end
