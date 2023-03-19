include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "crab.mm"
include "w3a.mm"
include "lshpset.mm"
include "eleq2d.mm"
include "neeq1.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem islshp
  let vv: setvar v
  let cS: class S
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vs: setvar s
  assume lshpset.v: |- V = ( Base ` W )
  assume lshpset.n: |- N = ( LSpan ` W )
  assume lshpset.s: |- S = ( LSubSp ` W )
  assume lshpset.h: |- H = ( LSHyp ` W )

  disjoint V v
  disjoint W v
  disjoint U v
  disjoint N w
  disjoint s w
  disjoint S s
  disjoint S w
  disjoint v w
  disjoint V w
  disjoint s v
  disjoint W s
  disjoint W w
  disjoint N s
  disjoint U s
  disjoint V s
  assert |- ( W e. X -> ( U e. H <-> ( U e. S /\ U =/= V /\ E. v e. V ( N ` ( U u. { v } ) ) = V ) ) )

  proof
    cW
    cX
    wcel
    #
    cU
    cH
    wcel
    cU
    vs
    cv
    #
    cV
    wne
    #
    @1
    vv
    cv
    csn
    #
    cun
    #
    cN
    cfv
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    wa
    #
    vs
    cS
    crab
    #
    wcel
    #
    cU
    cS
    wcel
    #
    cU
    cV
    wne
    #
    cU
    @3
    cun
    #
    cN
    cfv
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    w3a
    #
    @0
    cH
    @9
    cU
    vv
    cS
    cH
    cN
    cV
    cW
    cX
    vs
    lshpset.v
    lshpset.n
    lshpset.s
    lshpset.h
    lshpset
    eleq2d
    @10
    @11
    @12
    @16
    wa
    #
    wa
    @17
    @8
    @18
    vs
    cU
    cS
    @1
    cU
    wceq
    #
    @2
    @12
    @7
    @16
    @1
    cU
    cV
    neeq1
    @19
    @6
    @15
    vv
    cV
    @19
    @5
    @14
    cV
    @19
    @4
    @13
    cN
    @1
    cU
    @3
    uneq1
    fveq2d
    eqeq1d
    rexbidv
    anbi12d
    elrab
    @11
    @12
    @16
    3anass
    bitr4i
    syl6bb
end
