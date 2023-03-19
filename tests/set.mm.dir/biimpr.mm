include "wb.mm"
include "wi.mm"
include "wn.mm"
include "dfbi1.mm"
include "simprim.mm"
include "sylbi.mm"

theorem biimpr
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ps -> ph ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wn
    wi
    wn
    @1
    wph
    wps
    dfbi1
    @0
    @1
    simprim
    sylbi
end
