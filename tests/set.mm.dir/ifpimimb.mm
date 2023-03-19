include "wi.mm"
include "wif.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "dfifp2.mm"
include "imor.mm"
include "pm4.8.mm"
include "bicomi.mm"
include "orbi1i.mm"
include "id.mm"
include "orci.mm"
include "biantru.mm"
include "3bitri.mm"
include "pm4.64.mm"
include "pm4.81.mm"
include "biantrur.mm"
include "anbi12i.mm"
include "ifpim123g.mm"

theorem ifpimimb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps -> ch ) , ( th -> ta ) ) <-> ( if- ( ph , ps , th ) -> if- ( ph , ch , ta ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wth
    wta
    wi
    #
    wif
    wph
    @0
    wi
    #
    wph
    wn
    #
    @1
    wi
    #
    wa
    wph
    @3
    wi
    #
    @0
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
    @7
    wps
    wta
    wi
    #
    wo
    #
    @3
    wph
    wi
    #
    @1
    wo
    #
    wa
    #
    wa
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
    #
    wph
    @0
    @1
    dfifp2
    @2
    @10
    @4
    @15
    @2
    @3
    @0
    wo
    @6
    @10
    wph
    @0
    imor
    @3
    @5
    @0
    @5
    @3
    wph
    pm4.8
    bicomi
    orbi1i
    @9
    @6
    @7
    @8
    wph
    id
    #
    orci
    biantru
    3bitri
    @4
    wph
    @1
    wo
    @14
    @15
    wph
    @1
    pm4.64
    wph
    @13
    @1
    @13
    wph
    wph
    pm4.81
    bicomi
    orbi1i
    @12
    @14
    @7
    @11
    @18
    orci
    biantrur
    3bitri
    anbi12i
    @17
    @16
    wph
    wph
    wps
    wch
    wth
    wta
    ifpim123g
    bicomi
    3bitri
end
