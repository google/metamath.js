include "expcom.mm"
include "imp.mm"

theorem ancoms
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
