include "wif.mm"
include "wb.mm"
include "wi.mm"
include "wa.mm"
include "wo.mm"
include "dfbi2.mm"
include "ifpim1g.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi12i.mm"
include "an42.mm"
include "3bitri.mm"

theorem ifp1bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( if- ( ph , ch , th ) <-> if- ( ps , ch , th ) ) <-> ( ( ( ( ph -> ps ) \/ ( ch -> th ) ) /\ ( ( ph -> ps ) \/ ( th -> ch ) ) ) /\ ( ( ( ps -> ph ) \/ ( ch -> th ) ) /\ ( ( ps -> ph ) \/ ( th -> ch ) ) ) ) )

  proof
    wph
    wch
    wth
    wif
    #
    wps
    wch
    wth
    wif
    #
    wb
    @0
    @1
    wi
    #
    @1
    @0
    wi
    #
    wa
    wph
    wps
    wi
    #
    wch
    wth
    wi
    #
    wo
    #
    wps
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
    @4
    @8
    wo
    #
    @7
    @5
    wo
    #
    wa
    #
    wa
    @6
    @11
    wa
    @12
    @9
    wa
    wa
    @0
    @1
    dfbi2
    @2
    @10
    @3
    @13
    @2
    @9
    @6
    wa
    @10
    wph
    wps
    wch
    wth
    ifpim1g
    @9
    @6
    ancom
    bitri
    wps
    wph
    wch
    wth
    ifpim1g
    anbi12i
    @6
    @9
    @11
    @12
    an42
    3bitri
end
