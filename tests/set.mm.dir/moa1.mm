include "wi.mm"
include "ax-1.mm"
include "moimi.mm"

theorem moa1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E* x ( ph -> ps ) -> E* x ps )

  proof
    wps
    wph
    wps
    wi
    vx
    wps
    wph
    ax-1
    moimi
end
