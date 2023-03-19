include "wa.mm"
include "biimpi.mm"
include "sylancl.mm"

theorem sylanblc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylanblc.1: |- ( ph -> ps )
  assume sylanblc.2: |- ch
  assume sylanblc.3: |- ( ( ps /\ ch ) <-> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    sylanblc.1
    sylanblc.2
    wps
    wch
    wa
    wth
    sylanblc.3
    biimpi
    sylancl
end
