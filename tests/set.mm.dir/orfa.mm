include "wfal.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "orcom.mm"
include "df-or.mm"
include "bitri.mm"
include "fal.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "sylbi.mm"
include "orc.mm"
include "impbii.mm"

theorem orfa
  let wph: wff ph


  assert |- ( ( ph \/ F. ) <-> ph )

  proof
    wph
    wfal
    wo
    #
    wph
    @0
    wfal
    wn
    #
    wph
    wi
    #
    wph
    @0
    wfal
    wph
    wo
    @2
    wph
    wfal
    orcom
    wfal
    wph
    df-or
    bitri
    @1
    @2
    wph
    wi
    fal
    @1
    wph
    pm2.27
    ax-mp
    sylbi
    wph
    wfal
    orc
    impbii
end
