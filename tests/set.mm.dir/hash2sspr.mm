include "cpw.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "cpr.mm"
include "wrex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "wne.mm"
include "elss2prb.mm"
include "simpr.mm"
include "reximi.mm"
include "sylbi.mm"
include "sylbir.mm"

theorem hash2sspr
  let cP: class P
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vp: setvar p

  disjoint P a
  disjoint P b
  disjoint a b
  disjoint V a
  disjoint V b
  disjoint P p
  disjoint a p
  disjoint b p
  disjoint V p
  assert |- ( ( P e. ~P V /\ ( # ` P ) = 2 ) -> E. a e. V E. b e. V P = { a , b } )

  proof
    cP
    cV
    cpw
    #
    wcel
    cP
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    cP
    vp
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vp
    @0
    crab
    wcel
    #
    cP
    va
    cv
    #
    vb
    cv
    #
    cpr
    wceq
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    #
    @5
    @2
    vp
    cP
    @0
    @3
    cP
    wceq
    @4
    @1
    c2
    @3
    cP
    chash
    fveq2
    eqeq1d
    elrab
    @6
    @7
    @8
    wne
    #
    @9
    wa
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    @11
    va
    vb
    vp
    cP
    cV
    elss2prb
    @14
    @10
    va
    cV
    @13
    @9
    vb
    cV
    @12
    @9
    simpr
    reximi
    reximi
    sylbi
    sylbir
end
