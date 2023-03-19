include "cumgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "chash.mm"
include "c2.mm"
include "cvv.mm"
include "c1.mm"
include "wn.mm"
include "vex.mm"
include "hashsng.mm"
include "1ne2.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "mp2b.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "intnand.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edgumgr.mm"
include "sylan2b.mm"
include "nsyl3.mm"
include "nexdv.mm"

theorem umgredgnlp
  let vv: setvar v
  let cC: class C
  let cE: class E
  let cG: class G
  assume umgredgnlp.e: |- E = ( Edg ` G )

  disjoint C v
  disjoint E v
  disjoint G v
  assert |- ( ( G e. UMGraph /\ C e. E ) -> -. E. v C = { v } )

  proof
    cG
    cumgr
    wcel
    #
    cC
    cE
    wcel
    #
    wa
    #
    cC
    vv
    cv
    #
    csn
    #
    wceq
    #
    vv
    @5
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
    #
    c2
    wceq
    #
    wa
    #
    @2
    @5
    @8
    @6
    @5
    @8
    @4
    chash
    cfv
    #
    c2
    wceq
    #
    @3
    cvv
    wcel
    @10
    c1
    wceq
    #
    @11
    wn
    vv
    vex
    @3
    cvv
    hashsng
    @12
    @11
    c1
    c2
    wceq
    c1
    c2
    1ne2
    neii
    @10
    c1
    c2
    eqeq1
    mtbiri
    mp2b
    @5
    @7
    @10
    c2
    cC
    @4
    chash
    fveq2
    eqeq1d
    mtbiri
    intnand
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
    @13
    cC
    umgredgnlp.e
    eleq2i
    cC
    cG
    edgumgr
    sylan2b
    nsyl3
    nexdv
end
