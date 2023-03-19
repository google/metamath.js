include "wxo.mm"
include "wb.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-xor.mm"
include "nbi2.mm"
include "bitri.mm"

theorem xor2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) )

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
    wo
    wph
    wps
    wa
    wn
    wa
    wph
    wps
    df-xor
    wph
    wps
    nbi2
    bitri
end
