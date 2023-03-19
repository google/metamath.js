include "cusgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "usgredgss.mm"
include "sselda.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylib.mm"

theorem edgusgr
  let cE: class E
  let cG: class G
  let vx: setvar x


  assert |- ( ( G e. USGraph /\ E e. ( Edg ` G ) ) -> ( E e. ~P ( Vtx ` G ) /\ ( # ` E ) = 2 ) )

  proof
    cG
    cusgr
    wcel
    #
    cE
    cG
    cedg
    cfv
    #
    wcel
    wa
    cE
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cG
    cvtx
    cfv
    cpw
    #
    crab
    #
    wcel
    cE
    @5
    wcel
    cE
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    @0
    @1
    @6
    cE
    vx
    cG
    usgredgss
    sselda
    @4
    @8
    vx
    cE
    @5
    @2
    cE
    wceq
    @3
    @7
    c2
    @2
    cE
    chash
    fveq2
    eqeq1d
    elrab
    sylib
end
