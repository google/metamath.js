include "wi.mm"
include "wo.mm"
include "wb.mm"
include "olc.mm"
include "pm2.621.mm"
include "impbid2.mm"
include "orc.mm"
include "biimpr.mm"
include "syl5.mm"
include "impbii.mm"

theorem pm4.72
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) )

  proof
    wph
    wps
    wi
    #
    wps
    wph
    wps
    wo
    #
    wb
    #
    @0
    wps
    @1
    wps
    wph
    olc
    wph
    wps
    pm2.621
    impbid2
    wph
    @1
    @2
    wps
    wph
    wps
    orc
    wps
    @1
    biimpr
    syl5
    impbii
end
