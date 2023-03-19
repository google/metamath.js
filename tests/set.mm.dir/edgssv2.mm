include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edgusgr.mm"
include "sylan2b.mm"
include "elpwi.mm"
include "anim1i.mm"
include "syl.mm"
include "a1i.mm"
include "sseq2d.mm"
include "anbi1d.mm"
include "mpbird.mm"

theorem edgssv2
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  assume edgssv2.v: |- V = ( Vtx ` G )
  assume edgssv2.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ C e. E ) -> ( C C_ V /\ ( # ` C ) = 2 ) )

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
    #
    cC
    cV
    wss
    #
    cC
    chash
    cfv
    c2
    wceq
    #
    wa
    cC
    cG
    cvtx
    cfv
    #
    wss
    #
    @4
    wa
    #
    @2
    cC
    @5
    cpw
    wcel
    #
    @4
    wa
    #
    @7
    @1
    @0
    cC
    cG
    cedg
    cfv
    #
    wcel
    @9
    cE
    @10
    cC
    edgssv2.e
    eleq2i
    cC
    cG
    edgusgr
    sylan2b
    @8
    @6
    @4
    cC
    @5
    elpwi
    anim1i
    syl
    @2
    @3
    @6
    @4
    @2
    cV
    @5
    cC
    cV
    @5
    wceq
    @2
    edgssv2.v
    a1i
    sseq2d
    anbi1d
    mpbird
end
