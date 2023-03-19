include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "elfvex.mm"
include "eleq2s.mm"

theorem 1vgrex
  let cG: class G
  let cN: class N
  let cV: class V
  assume 1vgrex.v: |- V = ( Vtx ` G )


  assert |- ( N e. V -> G e. _V )

  proof
    cG
    cvv
    wcel
    cN
    cG
    cvtx
    cfv
    cV
    cN
    cG
    cvtx
    elfvex
    1vgrex.v
    eleq2s
end
