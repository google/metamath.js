include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cvv.mm"
include "df-br.mm"
include "elfvex.mm"
include "sylbi.mm"

theorem ulmscl
  let cS: class S
  let cF: class F
  let cG: class G


  assert |- ( F ( ~~>u ` S ) G -> S e. _V )

  proof
    cF
    cG
    cS
    culm
    cfv
    #
    wbr
    cF
    cG
    cop
    #
    @0
    wcel
    cS
    cvv
    wcel
    cF
    cG
    @0
    df-br
    @1
    cS
    culm
    elfvex
    sylbi
end
