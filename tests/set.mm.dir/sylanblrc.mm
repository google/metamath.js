include "wa.mm"
include "biimpri.mm"
include "sylancl.mm"

theorem sylanblrc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylanblrc.1: |- ( ph -> ps )
  assume sylanblrc.2: |- ch
  assume sylanblrc.3: |- ( th <-> ( ps /\ ch ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    sylanblrc.1
    sylanblrc.2
    wth
    wps
    wch
    wa
    sylanblrc.3
    biimpri
    sylancl
end
