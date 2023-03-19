include "wtru.mm"
include "tru.mm"
include "nfth.mm"

theorem nftru
  let vx: setvar x


  assert |- F/ x T.

  proof
    wtru
    vx
    tru
    nfth
end
