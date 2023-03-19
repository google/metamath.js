include "wa.mm"
include "wxo.mm"
include "wo.mm"
include "wcad.mm"
include "orc.mm"
include "df-cad.mm"
include "sylibr.mm"

theorem cad11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps ) -> cadd ( ph , ps , ch ) )

  proof
    wph
    wps
    wa
    #
    @0
    wch
    wph
    wps
    wxo
    wa
    #
    wo
    wph
    wps
    wch
    wcad
    @0
    @1
    orc
    wph
    wps
    wch
    df-cad
    sylibr
end
