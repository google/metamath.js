include "sylbir.mm"
include "sylib.mm"

theorem 3imtr3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3imtr3.1: |- ( ph -> ps )
  assume 3imtr3.2: |- ( ph <-> ch )
  assume 3imtr3.3: |- ( ps <-> th )


  assert |- ( ch -> th )

  proof
    wch
    wps
    wth
    wch
    wph
    wps
    3imtr3.2
    3imtr3.1
    sylbir
    3imtr3.3
    sylib
end
