include "wnf.mm"
include "wi.mm"
include "nfimt.mm"
include "imp.mm"

theorem nfimt2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( F/ x ph /\ F/ x ps ) -> F/ x ( ph -> ps ) )

  proof
    wph
    vx
    wnf
    wps
    vx
    wnf
    wph
    wps
    wi
    vx
    wnf
    wph
    wps
    vx
    nfimt
    imp
end
