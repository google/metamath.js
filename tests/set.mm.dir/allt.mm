include "wtru.mm"
include "tru.mm"
include "ax-gen.mm"

theorem allt
  let vx: setvar x


  assert |- A. x T.

  proof
    wtru
    vx
    tru
    ax-gen
end
