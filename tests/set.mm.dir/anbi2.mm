include "wb.mm"
include "id.mm"
include "anbi2d.mm"

theorem anbi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wch
    @0
    id
    anbi2d
end
