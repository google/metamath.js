include "wb.mm"
include "cab.mm"
include "wceq.mm"
include "bj-abbi.mm"
include "mpgbi.mm"

theorem bj-abbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-abbii.1: |- ( ph <-> ps )


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
    bj-abbi
    bj-abbii.1
    mpgbi
end
