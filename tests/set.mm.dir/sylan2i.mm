include "wi.mm"
include "a1i.mm"
include "sylan2d.mm"

theorem sylan2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylan2i.1: |- ( ph -> th )
  assume sylan2i.2: |- ( ps -> ( ( ch /\ th ) -> ta ) )


  assert |- ( ps -> ( ( ch /\ ph ) -> ta ) )

  proof
    wps
    wph
    wth
    wch
    wta
    wph
    wth
    wi
    wps
    sylan2i.1
    a1i
    sylan2i.2
    sylan2d
end
