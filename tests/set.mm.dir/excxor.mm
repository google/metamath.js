include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-xor.mm"
include "xor.mm"
include "ancom.mm"
include "orbi2i.mm"
include "3bitri.mm"

theorem excxor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) <-> ( ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) )

  proof
    wph
    wps
    wxo
    wph
    wps
    wb
    wn
    wph
    wps
    wn
    wa
    #
    wps
    wph
    wn
    #
    wa
    #
    wo
    @0
    @1
    wps
    wa
    #
    wo
    wph
    wps
    df-xor
    wph
    wps
    xor
    @2
    @3
    @0
    wps
    @1
    ancom
    orbi2i
    3bitri
end
