include "bj-spvv.mm"
include "mpg.mm"

theorem bj-chvarvv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-chvarvv.1: |- ( x = y -> ( ph <-> ps ) )
  assume bj-chvarvv.2: |- ph

  disjoint x y
  disjoint ps x
  assert |- ps

  proof
    wph
    wps
    vx
    wph
    wps
    vx
    vy
    bj-chvarvv.1
    bj-spvv
    bj-chvarvv.2
    mpg
end
