include "wn.mm"
include "wi.mm"
include "wo.mm"
include "wa.mm"
include "wif.mm"
include "pm2.521.mm"
include "orim1i.mm"
include "adantr.mm"
include "id.mm"
include "orci.mm"
include "a1i.mm"
include "jca.mm"
include "simpr.mm"
include "wb.mm"
include "pm4.81.mm"
include "bicomi.mm"
include "ifpbi1.mm"
include "ax-mp.mm"
include "dfifp4.mm"
include "bitri.mm"
include "ifpim123g.mm"
include "3imtr4i.mm"

theorem ifpimim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps -> ch ) , ( th -> ta ) ) -> ( if- ( ph , ps , th ) -> if- ( ph , ch , ta ) ) )

  proof
    wph
    wn
    #
    wph
    wi
    #
    wn
    #
    wps
    wch
    wi
    #
    wo
    #
    @1
    wth
    wta
    wi
    #
    wo
    #
    wa
    #
    wph
    @0
    wi
    #
    @3
    wo
    #
    wph
    wph
    wi
    #
    wth
    wch
    wi
    #
    wo
    #
    wa
    #
    @10
    wps
    wta
    wi
    #
    wo
    #
    @6
    wa
    #
    wa
    wph
    @3
    @5
    wif
    #
    wph
    wps
    wth
    wif
    wph
    wch
    wta
    wif
    wi
    @7
    @13
    @16
    @7
    @9
    @12
    @4
    @9
    @6
    @2
    @8
    @3
    @0
    wph
    pm2.521
    orim1i
    adantr
    @12
    @7
    @10
    @11
    wph
    id
    #
    orci
    a1i
    jca
    @7
    @15
    @6
    @15
    @7
    @10
    @14
    @18
    orci
    a1i
    @4
    @6
    simpr
    jca
    jca
    @17
    @1
    @3
    @5
    wif
    #
    @7
    wph
    @1
    wb
    @17
    @19
    wb
    @1
    wph
    wph
    pm4.81
    bicomi
    wph
    @1
    @3
    @5
    ifpbi1
    ax-mp
    @1
    @3
    @5
    dfifp4
    bitri
    wph
    wph
    wps
    wch
    wth
    wta
    ifpim123g
    3imtr4i
end
