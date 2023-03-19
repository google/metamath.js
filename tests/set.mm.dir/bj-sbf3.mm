include "wex.mm"
include "nfe1.mm"
include "sbf.mm"

theorem bj-sbf3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] E. x ph <-> E. x ph )

  proof
    wph
    vx
    wex
    vx
    vy
    wph
    vx
    nfe1
    sbf
end
