include "ax-1.mm"
include "imp.mm"

theorem simpl
  param wph: wff ph
  param wps: wff ps


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
