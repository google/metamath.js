include "wa.mm"
include "pm3.2.mm"
include "sylc.mm"

theorem jca
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume jca.1: |- ( ph -> ps )
  assume jca.2: |- ( ph -> ch )


  assert |- ( ph -> ( ps /\ ch ) )

  proof
    wph
    wps
    wch
    wps
    wch
    wa
    jca.1
    jca.2
    wps
    wch
    pm3.2
    sylc
end
