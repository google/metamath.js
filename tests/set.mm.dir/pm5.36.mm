include "wb.mm"
include "id.mm"
include "pm5.32ri.mm"

theorem pm5.36
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    @0
    id
    pm5.32ri
end
