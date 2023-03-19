include "wb.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "biimpri.mm"

theorem aibandbiaiaiffb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wi
    wps
    wph
    wi
    wa
    wph
    wps
    dfbi2
    biimpri
end
