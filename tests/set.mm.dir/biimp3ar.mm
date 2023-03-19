include "exbiri.mm"
include "3imp.mm"

theorem biimp3ar
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume biimp3a.1: |- ( ( ph /\ ps ) -> ( ch <-> th ) )


  assert |- ( ( ph /\ ps /\ th ) -> ch )

  proof
    wph
    wps
    wth
    wch
    wph
    wps
    wch
    wth
    biimp3a.1
    exbiri
    3imp
end
