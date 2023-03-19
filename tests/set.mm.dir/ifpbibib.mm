include "wb.mm"
include "wif.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "dfifp2.mm"
include "dfbi2.mm"
include "imbi2i.mm"
include "jcab.mm"
include "bitri.mm"
include "anbi12i.mm"
include "an4.mm"
include "ifpimimb.mm"
include "bitr3i.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem ifpbibib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ( ps <-> ch ) , ( th <-> ta ) ) <-> ( if- ( ph , ps , th ) <-> if- ( ph , ch , ta ) ) )

  proof
    wph
    wps
    wch
    wb
    #
    wth
    wta
    wb
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
    #
    wph
    wps
    wch
    wi
    #
    wi
    #
    @3
    wth
    wta
    wi
    #
    wi
    #
    wa
    #
    wph
    wch
    wps
    wi
    #
    wi
    #
    @3
    wta
    wth
    wi
    #
    wi
    #
    wa
    #
    wa
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
    wb
    #
    wph
    @0
    @1
    dfifp2
    @5
    @7
    @12
    wa
    #
    @9
    @14
    wa
    #
    wa
    @16
    @2
    @20
    @4
    @21
    @2
    wph
    @6
    @11
    wa
    #
    wi
    @20
    @0
    @22
    wph
    wps
    wch
    dfbi2
    imbi2i
    wph
    @6
    @11
    jcab
    bitri
    @4
    @3
    @8
    @13
    wa
    #
    wi
    @21
    @1
    @23
    @3
    wth
    wta
    dfbi2
    imbi2i
    @3
    @8
    @13
    jcab
    bitri
    anbi12i
    @7
    @12
    @9
    @14
    an4
    bitri
    @16
    @17
    @18
    wi
    #
    @18
    @17
    wi
    #
    wa
    @19
    @10
    @24
    @15
    @25
    @10
    wph
    @6
    @8
    wif
    @24
    wph
    @6
    @8
    dfifp2
    wph
    wps
    wch
    wth
    wta
    ifpimimb
    bitr3i
    @15
    wph
    @11
    @13
    wif
    @25
    wph
    @11
    @13
    dfifp2
    wph
    wch
    wps
    wta
    wth
    ifpimimb
    bitr3i
    anbi12i
    @17
    @18
    dfbi2
    bitr4i
    3bitri
end
