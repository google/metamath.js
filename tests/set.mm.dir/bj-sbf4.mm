include "wnf.mm"
include "nfnf1.mm"
include "sbf.mm"

theorem bj-sbf4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] F/ x ph <-> F/ x ph )

  proof
    wph
    vx
    wnf
    vx
    vy
    wph
    vx
    nfnf1
    sbf
end
