include "wa.mm"
include "sylancr.mm"

theorem eel021old
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume eel021.1: |- ph
  assume eel021.2: |- ( ( ps /\ ch ) -> th )
  assume eel021.3: |- ( ( ph /\ th ) -> ta )


  assert |- ( ( ps /\ ch ) -> ta )

  proof
    wps
    wch
    wa
    wph
    wth
    wta
    eel021.1
    eel021.2
    eel021.3
    sylancr
end
