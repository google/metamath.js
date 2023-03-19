include "wex.mm"
include "ax5e.mm"
include "ax-5.mm"
include "bj-cbvexiw.mm"

theorem bj-cbvexivw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvexivw.1: |- ( y = x -> ( ph -> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ph y
  assert |- ( E. x ph -> E. y ps )

  proof
    wph
    wps
    vx
    vy
    wps
    vy
    wex
    vx
    ax5e
    wph
    vy
    ax-5
    bj-cbvexivw.1
    bj-cbvexiw
end
