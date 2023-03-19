include "hbn1w.mm"

theorem ax10w
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ax10w.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( -. A. x ph -> A. x -. A. x ph )

  proof
    wph
    wps
    vx
    vy
    ax10w.1
    hbn1w
end
