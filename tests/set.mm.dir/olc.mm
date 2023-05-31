include "wn.mm"
include "ax-1.mm"
include "orrd.mm"

theorem olc
  param wph: wff ph
  param wps: wff ps


  assert |- ( ph -> ( ps \/ ph ) )

  proof
    wph
    wps
    wph
    wph
    wps
    wn
    ax-1
    orrd
end
