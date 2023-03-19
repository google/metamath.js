include "wif.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "df-or.mm"
include "ifpnot23.mm"
include "imbi1i.mm"
include "bitri.mm"
include "ifpim123g.mm"
include "pm4.64.mm"
include "orbi2i.mm"
include "anbi12i.mm"

theorem ifpor123g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( if- ( ph , ch , ta ) \/ if- ( ps , th , et ) ) <-> ( ( ( ( ph -> -. ps ) \/ ( ch \/ th ) ) /\ ( ( ps -> ph ) \/ ( ta \/ th ) ) ) /\ ( ( ( ph -> ps ) \/ ( ch \/ et ) ) /\ ( ( -. ps -> ph ) \/ ( ta \/ et ) ) ) ) )

  proof
    wph
    wch
    wta
    wif
    #
    wps
    wth
    wet
    wif
    #
    wo
    #
    wph
    wps
    wn
    #
    wi
    #
    wch
    wn
    #
    wth
    wi
    #
    wo
    #
    wps
    wph
    wi
    #
    wta
    wn
    #
    wth
    wi
    #
    wo
    #
    wa
    #
    wph
    wps
    wi
    #
    @5
    wet
    wi
    #
    wo
    #
    @3
    wph
    wi
    #
    @9
    wet
    wi
    #
    wo
    #
    wa
    #
    wa
    #
    @4
    wch
    wth
    wo
    #
    wo
    #
    @8
    wta
    wth
    wo
    #
    wo
    #
    wa
    #
    @13
    wch
    wet
    wo
    #
    wo
    #
    @16
    wta
    wet
    wo
    #
    wo
    #
    wa
    #
    wa
    @2
    wph
    @5
    @9
    wif
    #
    @1
    wi
    #
    @20
    @2
    @0
    wn
    #
    @1
    wi
    @32
    @0
    @1
    df-or
    @33
    @31
    @1
    wph
    wch
    wta
    ifpnot23
    imbi1i
    bitri
    wph
    wps
    @5
    wth
    @9
    wet
    ifpim123g
    bitri
    @12
    @25
    @19
    @30
    @7
    @22
    @11
    @24
    @6
    @21
    @4
    wch
    wth
    pm4.64
    orbi2i
    @10
    @23
    @8
    wta
    wth
    pm4.64
    orbi2i
    anbi12i
    @15
    @27
    @18
    @29
    @14
    @26
    @13
    wch
    wet
    pm4.64
    orbi2i
    @17
    @28
    @16
    wta
    wet
    pm4.64
    orbi2i
    anbi12i
    anbi12i
    bitri
end
