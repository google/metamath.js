include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wfal.mm"
include "dfbi1.mm"
include "pm2.21.mm"
include "imim2i.mm"
include "id.mm"
include "falim.mm"
include "ja.mm"
include "impbii.mm"
include "notbii.mm"
include "ax-1.mm"
include "pm2.43i.mm"
include "3bitri.mm"

theorem tbw-bijust
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ( ph -> ps ) -> ( ( ps -> ph ) -> F. ) ) -> F. ) )

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
    #
    wi
    #
    wn
    @0
    @1
    wfal
    wi
    #
    wi
    #
    wn
    #
    @5
    wfal
    wi
    #
    wph
    wps
    dfbi1
    @3
    @5
    @3
    @5
    @2
    @4
    @0
    @1
    wfal
    pm2.21
    imim2i
    @4
    @2
    @0
    @1
    wfal
    @2
    @2
    id
    @2
    falim
    ja
    imim2i
    impbii
    notbii
    @6
    @7
    @5
    wfal
    pm2.21
    @7
    @6
    @5
    wfal
    @7
    @6
    wi
    #
    @6
    @7
    ax-1
    @8
    falim
    ja
    pm2.43i
    impbii
    3bitri
end
