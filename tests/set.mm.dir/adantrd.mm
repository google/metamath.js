include "wa.mm"
include "simpl.mm"
include "syl5.mm"

theorem adantrd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume adantrd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( ps /\ th ) -> ch ) )

  proof
    wps
    wth
    wa
    wps
    wph
    wch
    wps
    wth
    simpl
    adantrd.1
    syl5
end
