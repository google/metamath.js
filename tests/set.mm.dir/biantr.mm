include "wb.mm"
include "id.mm"
include "bibi2d.mm"
include "biimparc.mm"

theorem biantr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) )

  proof
    wch
    wps
    wb
    #
    wph
    wch
    wb
    wph
    wps
    wb
    @0
    wch
    wps
    wph
    @0
    id
    bibi2d
    biimparc
end
