include "wo.mm"
include "wb.mm"
include "norbi.mm"
include "con1i.mm"

theorem nbior
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph <-> ps ) -> ( ph \/ ps ) )

  proof
    wph
    wps
    wo
    wph
    wps
    wb
    wph
    wps
    norbi
    con1i
end
