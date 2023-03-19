include "wb.mm"
include "w3a.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wif.mm"
include "simp1.mm"
include "simp2.mm"
include "imbi12d.mm"
include "notbid.mm"
include "simp3.mm"
include "anbi12d.mm"
include "dfifp2.mm"
include "3bitr4g.mm"

theorem ifpbi123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) /\ ( ta <-> et ) ) -> ( if- ( ph , ch , ta ) <-> if- ( ps , th , et ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wta
    wet
    wb
    #
    w3a
    #
    wph
    wch
    wi
    #
    wph
    wn
    #
    wta
    wi
    #
    wa
    wps
    wth
    wi
    #
    wps
    wn
    #
    wet
    wi
    #
    wa
    wph
    wch
    wta
    wif
    wps
    wth
    wet
    wif
    @3
    @4
    @7
    @6
    @9
    @3
    wph
    wps
    wch
    wth
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    imbi12d
    @3
    @5
    @8
    wta
    wet
    @3
    wph
    wps
    @10
    notbid
    @0
    @1
    @2
    simp3
    imbi12d
    anbi12d
    wph
    wch
    wta
    dfifp2
    wps
    wth
    wet
    dfifp2
    3bitr4g
end
