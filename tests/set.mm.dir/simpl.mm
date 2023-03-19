include "ax-1.mm"
include "imp.mm"

theorem simpl
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) -> ph )

  proof
    wph
    wps
    wph
    wph
    wps
    ax-1
    imp
end
