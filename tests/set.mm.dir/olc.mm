include "wn.mm"
include "ax-1.mm"
include "orrd.mm"

theorem olc
  let wph: wff ph
  let wps: wff ps


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
