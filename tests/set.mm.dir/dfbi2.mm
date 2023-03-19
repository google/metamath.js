include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "dfbi1.mm"
include "df-an.mm"
include "bitr4i.mm"

theorem dfbi2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) )

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
    @0
    @1
    wa
    wph
    wps
    dfbi1
    @0
    @1
    df-an
    bitr4i
end
