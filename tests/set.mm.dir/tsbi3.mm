include "wn.mm"
include "wo.mm"
include "wb.mm"
include "wi.mm"
include "biimpr.mm"
include "con34b.mm"
include "pm2.54.mm"
include "sylbi.mm"
include "syl.mm"
include "con3i.mm"
include "orri.mm"
include "a1i.mm"

theorem tsbi3
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( ph \/ -. ps ) \/ -. ( ph <-> ps ) ) )

  proof
    wph
    wps
    wn
    #
    wo
    #
    wph
    wps
    wb
    #
    wn
    #
    wo
    wth
    @1
    @3
    @2
    @1
    @2
    wps
    wph
    wi
    #
    @1
    wph
    wps
    biimpr
    @4
    wph
    wn
    @0
    wi
    @1
    wps
    wph
    con34b
    wph
    @0
    pm2.54
    sylbi
    syl
    con3i
    orri
    a1i
end
