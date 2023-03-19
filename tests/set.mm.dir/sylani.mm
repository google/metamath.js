include "wi.mm"
include "a1i.mm"
include "syland.mm"

theorem sylani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylani.1: |- ( ph -> ch )
  assume sylani.2: |- ( ps -> ( ( ch /\ th ) -> ta ) )


  assert |- ( ps -> ( ( ph /\ th ) -> ta ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wph
    wch
    wi
    wps
    sylani.1
    a1i
    sylani.2
    syland
end
