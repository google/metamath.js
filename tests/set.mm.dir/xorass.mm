include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "xor3.mm"
include "biass.mm"
include "xnor.mm"
include "bibi1i.mm"
include "bibi2i.mm"
include "3bitr3i.mm"
include "nbbn.mm"
include "3bitr2ri.mm"
include "df-xor.mm"
include "3bitr4i.mm"

theorem xorass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/_ ps ) \/_ ch ) <-> ( ph \/_ ( ps \/_ ch ) ) )

  proof
    wph
    wps
    wxo
    #
    wch
    wb
    wn
    #
    wph
    wps
    wch
    wxo
    #
    wb
    wn
    #
    @0
    wch
    wxo
    wph
    @2
    wxo
    @3
    wph
    @2
    wn
    #
    wb
    #
    @0
    wn
    #
    wch
    wb
    #
    @1
    wph
    @2
    xor3
    wph
    wps
    wb
    #
    wch
    wb
    wph
    wps
    wch
    wb
    #
    wb
    @7
    @5
    wph
    wps
    wch
    biass
    @8
    @6
    wch
    wph
    wps
    xnor
    bibi1i
    @9
    @4
    wph
    wps
    wch
    xnor
    bibi2i
    3bitr3i
    @0
    wch
    nbbn
    3bitr2ri
    @0
    wch
    df-xor
    wph
    @2
    df-xor
    3bitr4i
end
