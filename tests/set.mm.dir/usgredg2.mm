include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cdm.mm"
include "cfv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "usgrumgr.mm"
include "cvtx.mm"
include "eqid.mm"
include "umgredg2.mm"
include "sylan.mm"

theorem usgredg2
  let cE: class E
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume usgredg2.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. USGraph /\ X e. dom E ) -> ( # ` ( E ` X ) ) = 2 )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cX
    cE
    cdm
    wcel
    cX
    cE
    cfv
    chash
    cfv
    c2
    wceq
    cG
    usgrumgr
    cE
    cG
    cG
    cvtx
    cfv
    #
    cX
    @0
    eqid
    usgredg2.e
    umgredg2
    sylan
end
