include "wsb.mm"
include "bj-stdpc4v.mm"
include "mpg.mm"

theorem bj-sbtv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-sbtv.1: |- ph

  disjoint x y
  assert |- [ y / x ] ph

  proof
    wph
    wph
    vx
    vy
    wsb
    vx
    wph
    vx
    vy
    bj-stdpc4v
    bj-sbtv.1
    mpg
end
