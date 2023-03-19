include "biimpi.mm"
include "sylan.mm"

theorem sylanb
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume sylanb.1: |- ( ph <-> ps )
  assume sylanb.2: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    sylanb.1
    biimpi
    sylanb.2
    sylan
end
