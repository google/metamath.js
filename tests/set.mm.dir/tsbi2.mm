include "wo.mm"
include "wb.mm"
include "wn.mm"
include "wa.mm"
include "pm5.21.mm"
include "olcd.mm"
include "pm4.57.mm"
include "biimpi.mm"
include "orcd.mm"
include "pm2.61i.mm"
include "a1i.mm"

theorem tsbi2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( ph \/ ps ) \/ ( ph <-> ps ) ) )

  proof
    wph
    wps
    wo
    #
    wph
    wps
    wb
    #
    wo
    #
    wth
    wph
    wn
    wps
    wn
    wa
    #
    @2
    @3
    @1
    @0
    wph
    wps
    pm5.21
    olcd
    @3
    wn
    #
    @0
    @1
    @4
    @0
    wph
    wps
    pm4.57
    biimpi
    orcd
    pm2.61i
    a1i
end
