include "wceq.mm"
include "ctpos.mm"
include "tposeq.mm"
include "ax-mp.mm"

theorem tposeqi
  let cF: class F
  let cG: class G
  assume tposeqi.1: |- F = G


  assert |- tpos F = tpos G

  proof
    cF
    cG
    wceq
    cF
    ctpos
    cG
    ctpos
    wceq
    tposeqi.1
    cF
    cG
    tposeq
    ax-mp
end
