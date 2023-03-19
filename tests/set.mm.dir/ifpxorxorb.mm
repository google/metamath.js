include "wxo.mm"
include "wif.mm"
include "wb.mm"
include "wn.mm"
include "df-xor.mm"
include "ifpbi23.mm"
include "mp2an.mm"
include "ifpbibib.mm"
include "notbii.mm"
include "ifpnotnotb.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem ifpxorxorb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps \/_ ch ) , ( th \/_ ta ) ) <-> ( if- ( ph , ps , th ) \/_ if- ( ph , ch , ta ) ) )

  proof
    wph
    wps
    wch
    wxo
    #
    wth
    wta
    wxo
    #
    wif
    #
    wph
    wps
    wch
    wb
    #
    wn
    #
    wth
    wta
    wb
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
    wxo
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
    df-xor
    wth
    wta
    df-xor
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
    wb
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
    ifpbibib
    notbii
    wph
    @3
    @5
    ifpnotnotb
    @8
    @9
    df-xor
    3bitr4i
    bitri
end
