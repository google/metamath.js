include "wif.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ifpim123g.mm"
include "id.mm"
include "olci.mm"
include "biantrur.mm"
include "bicomi.mm"
include "biantru.mm"
include "anbi12i.mm"
include "bitri.mm"

theorem ifpim1g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( if- ( ph , ch , th ) -> if- ( ps , ch , th ) ) <-> ( ( ( ps -> ph ) \/ ( th -> ch ) ) /\ ( ( ph -> ps ) \/ ( ch -> th ) ) ) )

  proof
    wph
    wch
    wth
    wif
    wps
    wch
    wth
    wif
    wi
    wph
    wps
    wn
    #
    wi
    #
    wch
    wch
    wi
    #
    wo
    #
    wps
    wph
    wi
    wth
    wch
    wi
    wo
    #
    wa
    #
    wph
    wps
    wi
    wch
    wth
    wi
    wo
    #
    @0
    wph
    wi
    #
    wth
    wth
    wi
    #
    wo
    #
    wa
    #
    wa
    @4
    @6
    wa
    wph
    wps
    wch
    wch
    wth
    wth
    ifpim123g
    @5
    @4
    @10
    @6
    @4
    @5
    @3
    @4
    @2
    @1
    wch
    id
    olci
    biantrur
    bicomi
    @6
    @10
    @9
    @6
    @8
    @7
    wth
    id
    olci
    biantru
    bicomi
    anbi12i
    bitri
end
