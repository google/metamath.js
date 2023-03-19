include "wtru.mm"
include "tru.mm"
include "exiftru.mm"

theorem bj-extru
  let vx: setvar x


  assert |- E. x T.

  proof
    wtru
    vx
    tru
    exiftru
end
