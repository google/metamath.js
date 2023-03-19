include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "co.mm"
include "crab.mm"
include "wa.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem fusgreg2wsplem
  let vw: setvar w
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assume frgrhash2wsp.v: |- V = ( Vtx ` G )
  assume fusgreg2wsp.m: |- M = ( a e. V |-> { w e. ( 2 WSPathsN G ) | ( w ` 1 ) = a } )

  disjoint p w
  disjoint G a
  disjoint V a
  disjoint G w
  disjoint N a
  disjoint N w
  disjoint a w
  disjoint G b
  disjoint a b
  disjoint V b
  assert |- ( N e. V -> ( p e. ( M ` N ) <-> ( p e. ( 2 WSPathsN G ) /\ ( p ` 1 ) = N ) ) )

  proof
    cN
    cV
    wcel
    #
    vp
    cv
    #
    cN
    cM
    cfv
    #
    wcel
    @1
    c1
    vw
    cv
    #
    cfv
    #
    cN
    wceq
    #
    vw
    c2
    cG
    cwwspthsn
    co
    #
    crab
    #
    wcel
    @1
    @6
    wcel
    c1
    @1
    cfv
    #
    cN
    wceq
    #
    wa
    @0
    @2
    @7
    @1
    va
    cN
    @4
    va
    cv
    #
    wceq
    #
    vw
    @6
    crab
    @7
    cV
    cM
    @10
    cN
    wceq
    @11
    @5
    vw
    @6
    @10
    cN
    @4
    eqeq2
    rabbidv
    fusgreg2wsp.m
    @5
    vw
    @6
    c2
    cG
    cwwspthsn
    ovex
    rabex
    fvmpt
    eleq2d
    @5
    @9
    vw
    @1
    @6
    vw
    vp
    weq
    @4
    @8
    cN
    c1
    @3
    @1
    fveq1
    eqeq1d
    elrab
    syl6bb
end
