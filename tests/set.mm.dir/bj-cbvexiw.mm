include "wex.mm"
include "spimeh.mm"
include "bj-exlime.mm"

theorem bj-cbvexiw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvexiw.1: |- ( E. x E. y ps -> E. y ps )
  assume bj-cbvexiw.2: |- ( ph -> A. y ph )
  assume bj-cbvexiw.3: |- ( y = x -> ( ph -> ps ) )

  disjoint x y
  assert |- ( E. x ph -> E. y ps )

  proof
    wph
    wps
    vy
    wex
    vx
    bj-cbvexiw.1
    wph
    wps
    vy
    vx
    bj-cbvexiw.2
    bj-cbvexiw.3
    spimeh
    bj-exlime
end
