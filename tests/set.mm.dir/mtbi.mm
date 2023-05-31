include "biimpri.mm"
include "mto.mm"

theorem mtbi
  param wph: wff ph
  param wps: wff ps
  assume mtbi.1: |- -. ph
  assume mtbi.2: |- ( ph <-> ps )


  assert |- -. ps

  proof
    wps
    wph
    mtbi.1
    wph
    wps
    mtbi.2
    biimpri
    mto
end
