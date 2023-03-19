include "wxo.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "xor2.mm"
include "simplbi.mm"

theorem xoror
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) -> ( ph \/ ps ) )

  proof
    wph
    wps
    wxo
    wph
    wps
    wo
    wph
    wps
    wa
    wn
    wph
    wps
    xor2
    simplbi
end
