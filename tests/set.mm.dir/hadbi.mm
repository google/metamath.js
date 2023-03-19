include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "whad.mm"
include "df-xor.mm"
include "df-had.mm"
include "xnor.mm"
include "bibi1i.mm"
include "nbbn.mm"
include "bitri.mm"
include "3bitr4i.mm"

theorem hadbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) )

  proof
    wph
    wps
    wxo
    #
    wch
    wxo
    @0
    wch
    wb
    wn
    #
    wph
    wps
    wch
    whad
    wph
    wps
    wb
    #
    wch
    wb
    #
    @0
    wch
    df-xor
    wph
    wps
    wch
    df-had
    @3
    @0
    wn
    #
    wch
    wb
    @1
    @2
    @4
    wch
    wph
    wps
    xnor
    bibi1i
    @0
    wch
    nbbn
    bitri
    3bitr4i
end
