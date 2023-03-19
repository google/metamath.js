include "wa.mm"
include "wb.mm"
include "biimpi.mm"
include "biimp3a.mm"

theorem bi123impia
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi123impia.1: |- ( ( ph /\ ps ) <-> ( ch <-> th ) )


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
    wb
    bi123impia.1
    biimpi
    biimp3a
end
