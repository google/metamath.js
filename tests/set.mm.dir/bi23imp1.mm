include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "syl6bi.mm"
include "3imp.mm"

theorem bi23imp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi23imp1.1: |- ( ph -> ( ps <-> ( ch <-> th ) ) )


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
    bi23imp1.1
    wch
    wth
    biimp
    syl6bi
    3imp
end
