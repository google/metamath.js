include "wnan.mm"
include "wif.mm"
include "wa.mm"
include "wn.mm"
include "wb.mm"
include "df-nan.mm"
include "ifpbi23.mm"
include "mp2an.mm"
include "ifpananb.mm"
include "notbii.mm"
include "ifpnotnotb.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem ifpnannanb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps -/\ ch ) , ( th -/\ ta ) ) <-> ( if- ( ph , ps , th ) -/\ if- ( ph , ch , ta ) ) )

  proof
    wph
    wps
    wch
    wnan
    #
    wth
    wta
    wnan
    #
    wif
    #
    wph
    wps
    wch
    wa
    #
    wn
    #
    wth
    wta
    wa
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
    wnan
    #
    @0
    @4
    wb
    @1
    @6
    wb
    @2
    @7
    wb
    wps
    wch
    df-nan
    wth
    wta
    df-nan
    @0
    @4
    @1
    @6
    wph
    ifpbi23
    mp2an
    wph
    @3
    @5
    wif
    #
    wn
    @8
    @9
    wa
    #
    wn
    @7
    @10
    @11
    @12
    wph
    wps
    wch
    wth
    wta
    ifpananb
    notbii
    wph
    @3
    @5
    ifpnotnotb
    @8
    @9
    df-nan
    3bitr4i
    bitri
end
