include "wo.mm"
include "orc.mm"
include "olc.mm"
include "pm5.21ni.mm"

theorem norbi
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph \/ ps ) -> ( ph <-> ps ) )

  proof
    wph
    wph
    wps
    wo
    wps
    wph
    wps
    orc
    wps
    wph
    olc
    pm5.21ni
end
