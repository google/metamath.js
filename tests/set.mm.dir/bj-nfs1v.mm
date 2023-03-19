include "wsb.mm"
include "bj-hbs1.mm"
include "nf5i.mm"

theorem bj-nfs1v
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
    bj-hbs1
    nf5i
end
