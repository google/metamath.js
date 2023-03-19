include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edgusgr.mm"
include "sylan2b.mm"
include "simprd.mm"

theorem usgredgppr
  let cC: class C
  let cE: class E
  let cG: class G
  assume usgredgppr.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ C e. E ) -> ( # ` C ) = 2 )

  proof
    cG
    cusgr
    wcel
    #
    cC
    cE
    wcel
    #
    wa
    cC
    cG
    cvtx
    cfv
    cpw
    wcel
    #
    cC
    chash
    cfv
    c2
    wceq
    #
    @1
    @0
    cC
    cG
    cedg
    cfv
    #
    wcel
    @2
    @3
    wa
    cE
    @4
    cC
    usgredgppr.e
    eleq2i
    cC
    cG
    edgusgr
    sylan2b
    simprd
end
