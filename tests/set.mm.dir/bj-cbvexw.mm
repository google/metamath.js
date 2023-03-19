include "wex.mm"
include "weq.mm"
include "wb.mm"
include "equcoms.mm"
include "biimpd.mm"
include "bj-cbvexiw.mm"
include "biimprd.mm"
include "impbii.mm"

theorem bj-cbvexw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvexw.1: |- ( E. x E. y ps -> E. y ps )
  assume bj-cbvexw.2: |- ( ph -> A. y ph )
  assume bj-cbvexw.3: |- ( E. y E. x ph -> E. x ph )
  assume bj-cbvexw.4: |- ( ps -> A. x ps )
  assume bj-cbvexw.5: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  assert |- ( E. x ph <-> E. y ps )

  proof
    wph
    vx
    wex
    wps
    vy
    wex
    wph
    wps
    vx
    vy
    bj-cbvexw.1
    bj-cbvexw.2
    vy
    vx
    weq
    wph
    wps
    wph
    wps
    wb
    vx
    vy
    bj-cbvexw.5
    equcoms
    biimpd
    bj-cbvexiw
    wps
    wph
    vy
    vx
    bj-cbvexw.3
    bj-cbvexw.4
    vx
    vy
    weq
    wph
    wps
    bj-cbvexw.5
    biimprd
    bj-cbvexiw
    impbii
end
