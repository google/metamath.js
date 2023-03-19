include "wsb.mm"
include "hbs1.mm"
include "nf5i.mm"

theorem nfs1v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- F/ x [ y / x ] ph

  proof
    wph
    vx
    vy
    wsb
    vx
    wph
    vx
    vy
    hbs1
    nf5i
end
