include "wn.mm"
include "hbn1.mm"

theorem modal-5
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. A. x -. ph -> A. x -. A. x -. ph )

  proof
    wph
    wn
    vx
    hbn1
end
