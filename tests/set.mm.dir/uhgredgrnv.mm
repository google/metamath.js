include "cuhgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "wa.mm"
include "cpw.mm"
include "wi.mm"
include "edguhgr.mm"
include "elelpwi.mm"
include "expcom.mm"
include "syl.mm"
include "3impia.mm"

theorem uhgredgrnv
  let cE: class E
  let cG: class G
  let cN: class N


  assert |- ( ( G e. UHGraph /\ E e. ( Edg ` G ) /\ N e. E ) -> N e. ( Vtx ` G ) )

  proof
    cG
    cuhgr
    wcel
    #
    cE
    cG
    cedg
    cfv
    wcel
    #
    cN
    cE
    wcel
    #
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    @0
    @1
    wa
    cE
    @3
    cpw
    wcel
    #
    @2
    @4
    wi
    cE
    cG
    edguhgr
    @2
    @5
    @4
    cN
    cE
    @3
    elelpwi
    expcom
    syl
    3impia
end
