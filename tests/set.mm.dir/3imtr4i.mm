include "sylbi.mm"
include "sylibr.mm"

theorem 3imtr4i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3imtr4.1: |- ( ph -> ps )
  assume 3imtr4.2: |- ( ch <-> ph )
  assume 3imtr4.3: |- ( th <-> ps )


  assert |- ( ch -> th )

  proof
    wch
    wps
    wth
    wch
    wph
    wps
    3imtr4.2
    3imtr4.1
    sylbi
    3imtr4.3
    sylibr
end
