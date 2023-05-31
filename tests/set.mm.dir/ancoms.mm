include "expcom.mm"
include "imp.mm"

theorem ancoms
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume ancoms.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ps /\ ph ) -> ch )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    ancoms.1
    expcom
    imp
end
