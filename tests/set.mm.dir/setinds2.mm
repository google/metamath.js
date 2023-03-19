include "nfv.mm"
include "setinds2f.mm"

theorem setinds2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume setinds2.1: |- ( x = y -> ( ph <-> ps ) )
  assume setinds2.2: |- ( A. y e. x ps -> ph )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ph

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    setinds2.1
    setinds2.2
    setinds2f
end
