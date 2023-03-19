include "ax-10.mm"

theorem hbn1
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x ph -> A. x -. A. x ph )

  proof
    wph
    vx
    ax-10
end
