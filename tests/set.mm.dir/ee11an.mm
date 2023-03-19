include "ex.mm"
include "sylc.mm"

theorem ee11an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ee11an.1: |- ( ph -> ps )
  assume ee11an.2: |- ( ph -> ch )
  assume ee11an.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wth
    ee11an.1
    ee11an.2
    wps
    wch
    wth
    ee11an.3
    ex
    sylc
end
