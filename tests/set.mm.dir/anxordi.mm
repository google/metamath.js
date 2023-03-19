include "wb.mm"
include "wn.mm"
include "wa.mm"
include "wxo.mm"
include "xordi.mm"
include "df-xor.mm"
include "anbi2i.mm"
include "3bitr4i.mm"

theorem anxordi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps \/_ ch ) ) <-> ( ( ph /\ ps ) \/_ ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    wb
    wn
    #
    wa
    wph
    wps
    wa
    #
    wph
    wch
    wa
    #
    wb
    wn
    wph
    wps
    wch
    wxo
    #
    wa
    @1
    @2
    wxo
    wph
    wps
    wch
    xordi
    @3
    @0
    wph
    wps
    wch
    df-xor
    anbi2i
    @1
    @2
    df-xor
    3bitr4i
end
