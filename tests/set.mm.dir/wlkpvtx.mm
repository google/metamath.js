include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wcel.mm"
include "wi.mm"
include "wlkp.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"

theorem wlkpvtx
  let cP: class P
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  assume wlkpvtx.v: |- V = ( Vtx ` G )


  assert |- ( F ( Walks ` G ) P -> ( N e. ( 0 ... ( # ` F ) ) -> ( P ` N ) e. V ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    cfz
    co
    #
    cV
    cP
    wf
    #
    cN
    @0
    wcel
    #
    cN
    cP
    cfv
    cV
    wcel
    #
    wi
    cP
    cF
    cG
    cV
    wlkpvtx.v
    wlkp
    @1
    @2
    @3
    @0
    cV
    cN
    cP
    ffvelrn
    ex
    syl
end
