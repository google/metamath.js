include "expcom.mm"
include "mpan9.mm"

theorem sylan
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume sylan.1: |- ( ph -> ps )
  assume sylan.2: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    sylan.1
    wps
    wch
    wth
    sylan.2
    expcom
    mpan9
end
