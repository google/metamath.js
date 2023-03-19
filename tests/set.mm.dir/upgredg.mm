include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "ciedg.mm"
include "crn.mm"
include "cedg.mm"
include "edgval.mm"
include "a1i.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "upgrf.mm"
include "frn.mm"
include "syl.mm"
include "sseld.mm"
include "sylbid.mm"
include "imp.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "hashle2prv.mm"
include "biimpa.mm"
include "sylbi.mm"

theorem upgredg
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
  assert |- ( ( G e. UPGraph /\ C e. E ) -> E. a e. V E. b e. V C = { a , b } )

  proof
    cG
    cupgr
    wcel
    #
    cC
    cE
    wcel
    #
    wa
    cC
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    cV
    cpw
    c0
    csn
    cdif
    #
    crab
    #
    wcel
    #
    cC
    va
    cv
    vb
    cv
    cpr
    wceq
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @0
    @1
    @7
    @0
    @1
    cC
    cG
    ciedg
    cfv
    #
    crn
    #
    wcel
    @7
    @0
    cE
    @10
    cC
    @0
    cE
    cG
    cedg
    cfv
    #
    @10
    upgredg.e
    @11
    @10
    wceq
    @0
    cG
    edgval
    a1i
    syl5eq
    eleq2d
    @0
    @10
    @6
    cC
    @0
    @9
    cdm
    #
    @6
    @9
    wf
    @10
    @6
    wss
    vx
    @9
    cG
    cV
    upgredg.v
    @9
    eqid
    upgrf
    @12
    @6
    @9
    frn
    syl
    sseld
    sylbid
    imp
    @7
    cC
    @5
    wcel
    #
    cC
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    wa
    @8
    @4
    @15
    vx
    cC
    @5
    @2
    cC
    wceq
    @3
    @14
    c2
    cle
    @2
    cC
    chash
    fveq2
    breq1d
    elrab
    @13
    @15
    @8
    cC
    cV
    va
    vb
    hashle2prv
    biimpa
    sylbi
    syl
end
