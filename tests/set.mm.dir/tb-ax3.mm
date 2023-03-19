include "peirce.mm"

theorem tb-ax3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ph ) -> ph )

  proof
    wph
    wps
    peirce
end
