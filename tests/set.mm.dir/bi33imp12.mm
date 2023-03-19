include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "syl6.mm"
include "3imp.mm"

theorem bi33imp12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi33imp12.1: |- ( ph -> ( ps -> ( ch <-> th ) ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wb
    wch
    wth
    wi
    bi33imp12.1
    wch
    wth
    biimp
    syl6
    3imp
end
