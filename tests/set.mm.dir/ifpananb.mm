include "wa.mm"
include "wif.mm"
include "wn.mm"
include "wo.mm"
include "wb.mm"
include "anor.mm"
include "ifpbi23.mm"
include "mp2an.mm"
include "ifpororb.mm"
include "ifpnotnotb.mm"
include "orbi12i.mm"
include "bitri.mm"
include "notbii.mm"
include "3bitr4i.mm"

theorem ifpananb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps /\ ch ) , ( th /\ ta ) ) <-> ( if- ( ph , ps , th ) /\ if- ( ph , ch , ta ) ) )

  proof
    wph
    wps
    wch
    wa
    #
    wth
    wta
    wa
    #
    wif
    #
    wph
    wps
    wn
    #
    wch
    wn
    #
    wo
    #
    wn
    #
    wth
    wn
    #
    wta
    wn
    #
    wo
    #
    wn
    #
    wif
    #
    wph
    wps
    wth
    wif
    #
    wph
    wch
    wta
    wif
    #
    wa
    #
    @0
    @6
    wb
    @1
    @10
    wb
    @2
    @11
    wb
    wps
    wch
    anor
    wth
    wta
    anor
    @0
    @6
    @1
    @10
    wph
    ifpbi23
    mp2an
    wph
    @5
    @9
    wif
    #
    wn
    @12
    wn
    #
    @13
    wn
    #
    wo
    #
    wn
    @11
    @14
    @15
    @18
    @15
    wph
    @3
    @7
    wif
    #
    wph
    @4
    @8
    wif
    #
    wo
    @18
    wph
    @3
    @4
    @7
    @8
    ifpororb
    @19
    @16
    @20
    @17
    wph
    wps
    wth
    ifpnotnotb
    wph
    wch
    wta
    ifpnotnotb
    orbi12i
    bitri
    notbii
    wph
    @5
    @9
    ifpnotnotb
    @12
    @13
    anor
    3bitr4i
    bitri
end
