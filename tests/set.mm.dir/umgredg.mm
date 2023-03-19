include "cumgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "wrex.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "chash.mm"
include "c2.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edgumgr.mm"
include "sylan2b.mm"
include "hash2prde.mm"
include "wi.mm"
include "eleq1.mm"
include "wss.mm"
include "prex.mm"
include "elpw.mm"
include "vex.mm"
include "prss.mm"
include "sseq2i.mm"
include "sylbbr.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "adantrd.mm"
include "adantl.mm"
include "imdistanri.mm"
include "ex.mm"
include "2eximdv.mm"
include "mpd.mm"
include "syl.mm"
include "r2ex.mm"
include "sylibr.mm"

theorem umgredg
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vc: setvar c
  assume upgredg.v: |- V = ( Vtx ` G )
  assume upgredg.e: |- E = ( Edg ` G )

  disjoint C a
  disjoint C b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint V a
  disjoint V b
  disjoint C x
  disjoint G x
  disjoint V x
  disjoint C c
  disjoint a c
  disjoint b c
  disjoint V c
  assert |- ( ( G e. UMGraph /\ C e. E ) -> E. a e. V E. b e. V ( a =/= b /\ C = { a , b } ) )

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
    va
    cv
    #
    cV
    wcel
    vb
    cv
    #
    cV
    wcel
    wa
    #
    @3
    @4
    wne
    #
    cC
    @3
    @4
    cpr
    #
    wceq
    #
    wa
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    @9
    vb
    cV
    wrex
    va
    cV
    wrex
    @2
    cC
    cG
    cvtx
    cfv
    #
    cpw
    #
    wcel
    #
    cC
    chash
    cfv
    c2
    wceq
    #
    wa
    #
    @11
    @1
    @0
    cC
    cG
    cedg
    cfv
    #
    wcel
    @16
    cE
    @17
    cC
    upgredg.e
    eleq2i
    cC
    cG
    edgumgr
    sylan2b
    @16
    @9
    vb
    wex
    va
    wex
    @11
    cC
    @13
    va
    vb
    hash2prde
    @16
    @9
    @10
    va
    vb
    @16
    @9
    @10
    @9
    @16
    @5
    @8
    @16
    @5
    wi
    @6
    @8
    @14
    @5
    @15
    @8
    @14
    @7
    @13
    wcel
    #
    @5
    cC
    @7
    @13
    eleq1
    @18
    @7
    @12
    wss
    #
    @5
    @7
    @12
    @3
    @4
    prex
    elpw
    @5
    @7
    cV
    wss
    @19
    @3
    @4
    cV
    va
    vex
    vb
    vex
    prss
    cV
    @12
    @7
    upgredg.v
    sseq2i
    sylbbr
    sylbi
    syl6bi
    adantrd
    adantl
    imdistanri
    ex
    2eximdv
    mpd
    syl
    @9
    va
    vb
    cV
    cV
    r2ex
    sylibr
end
