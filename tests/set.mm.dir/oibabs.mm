include "wo.mm"
include "wb.mm"
include "wi.mm"
include "norbi.mm"
include "id.mm"
include "ja.mm"
include "ax-1.mm"
include "impbii.mm"

theorem oibabs
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) )

  proof
    wph
    wps
    wo
    #
    wph
    wps
    wb
    #
    wi
    @1
    @0
    @1
    @1
    wph
    wps
    norbi
    @1
    id
    ja
    @1
    @0
    ax-1
    impbii
end
