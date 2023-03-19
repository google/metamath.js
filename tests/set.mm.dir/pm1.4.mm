include "wo.mm"
include "olc.mm"
include "orc.mm"
include "jaoi.mm"

theorem pm1.4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) -> ( ps \/ ph ) )

  proof
    wph
    wps
    wph
    wo
    wps
    wph
    wps
    olc
    wps
    wph
    orc
    jaoi
end
