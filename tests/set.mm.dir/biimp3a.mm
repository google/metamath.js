include "wa.mm"
include "biimpa.mm"
include "3impa.mm"

theorem biimp3a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume biimp3a.1: |- ( ( ph /\ ps ) -> ( ch <-> th ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wa
    wch
    wth
    biimp3a.1
    biimpa
    3impa
end
