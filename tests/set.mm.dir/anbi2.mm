include "wb.mm"
include "id.mm"
include "anbi2d.mm"

theorem anbi2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


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
