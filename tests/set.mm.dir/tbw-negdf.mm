include "wn.mm"
include "wfal.mm"
include "wi.mm"
include "wb.mm"
include "pm2.21.mm"
include "ax-1.mm"
include "falim.mm"
include "ja.mm"
include "pm2.43i.mm"
include "impbii.mm"
include "tbw-bijust.mm"
include "mpbi.mm"

theorem tbw-negdf
  let wph: wff ph


  assert |- ( ( ( -. ph -> ( ph -> F. ) ) -> ( ( ( ph -> F. ) -> -. ph ) -> F. ) ) -> F. )

  proof
    wph
    wn
    #
    wph
    wfal
    wi
    #
    wb
    @0
    @1
    wi
    @1
    @0
    wi
    #
    wfal
    wi
    wi
    wfal
    wi
    @0
    @1
    wph
    wfal
    pm2.21
    @1
    @0
    wph
    wfal
    @2
    @0
    @1
    ax-1
    @2
    falim
    ja
    pm2.43i
    impbii
    @0
    @1
    tbw-bijust
    mpbi
end
