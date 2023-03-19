include "wb.mm"
include "cab.mm"
include "wceq.mm"
include "abbi.mm"
include "mpgbi.mm"

theorem abbii
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume abbii.1: |- ( ph <-> ps )


  assert |- { x | ph } = { x | ps }

  proof
    wph
    wps
    wb
    wph
    vx
    cab
    wps
    vx
    cab
    wceq
    vx
    wph
    wps
    vx
    abbi
    abbii.1
    mpgbi
end
