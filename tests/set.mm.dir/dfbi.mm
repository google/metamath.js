include "wb.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "biimpi.mm"
include "biimpri.mm"
include "pm3.2i.mm"

theorem dfbi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wi
    wps
    wph
    wi
    wa
    #
    wi
    @1
    @0
    wi
    @0
    @1
    wph
    wps
    dfbi2
    #
    biimpi
    @0
    @1
    @2
    biimpri
    pm3.2i
end
