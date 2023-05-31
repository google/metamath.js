include "wa.mm"
include "simpl.mm"
include "syl.mm"

theorem simpld
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume simpld.1: |- ( ph -> ( ps /\ ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wa
    wps
    simpld.1
    wps
    wch
    simpl
    syl
end
