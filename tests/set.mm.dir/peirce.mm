include "wi.mm"
include "simplim.mm"
include "id.mm"
include "ja.mm"

theorem peirce
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ph ) -> ph )

  proof
    wph
    wps
    wi
    wph
    wph
    wph
    wps
    simplim
    wph
    id
    ja
end
