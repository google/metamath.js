include "wi.mm"
include "id.mm"
include "bj-nimni.mm"

theorem bj-bijust0
  let wph: wff ph


  assert |- -. ( ( ph -> ph ) -> -. ( ph -> ph ) )

  proof
    wph
    wph
    wi
    wph
    id
    bj-nimni
end
