include "wcel.mm"
include "clsh.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "crab.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "clspn.mm"
include "clss.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "neeq2d.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "rexeqbidv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-lshyp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem lshpset
  let vv: setvar v
  let cS: class S
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  assume lshpset.v: |- V = ( Base ` W )
  assume lshpset.n: |- N = ( LSpan ` W )
  assume lshpset.s: |- S = ( LSubSp ` W )
  assume lshpset.h: |- H = ( LSHyp ` W )

  disjoint S s
  disjoint V v
  disjoint s v
  disjoint W s
  disjoint W v
  disjoint N w
  disjoint s w
  disjoint S w
  disjoint v w
  disjoint V w
  disjoint W w
  assert |- ( W e. X -> H = { s e. S | ( s =/= V /\ E. v e. V ( N ` ( s u. { v } ) ) = V ) } )

  proof
    cW
    cX
    wcel
    #
    cH
    cW
    clsh
    cfv
    #
    vs
    cv
    #
    cV
    wne
    #
    @2
    vv
    cv
    csn
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
    lshpset.h
    @0
    cW
    cvv
    wcel
    @1
    @9
    wceq
    cW
    cX
    elex
    vw
    cW
    @2
    vw
    cv
    #
    cbs
    cfv
    #
    wne
    #
    @4
    @10
    clspn
    cfv
    #
    cfv
    #
    @11
    wceq
    #
    vv
    @11
    wrex
    #
    wa
    #
    vs
    @10
    clss
    cfv
    #
    crab
    @9
    cvv
    clsh
    @10
    cW
    wceq
    #
    @17
    @8
    vs
    @18
    cS
    @19
    @18
    cW
    clss
    cfv
    #
    cS
    @10
    cW
    clss
    fveq2
    lshpset.s
    syl6eqr
    @19
    @12
    @3
    @16
    @7
    @19
    @11
    cV
    @2
    @19
    @11
    cW
    cbs
    cfv
    cV
    @10
    cW
    cbs
    fveq2
    lshpset.v
    syl6eqr
    #
    neeq2d
    @19
    @15
    @6
    vv
    @11
    cV
    @21
    @19
    @14
    @5
    @11
    cV
    @19
    @4
    @13
    cN
    @19
    @13
    cW
    clspn
    cfv
    cN
    @10
    cW
    clspn
    fveq2
    lshpset.n
    syl6eqr
    fveq1d
    @21
    eqeq12d
    rexeqbidv
    anbi12d
    rabeqbidv
    vw
    vv
    vs
    df-lshyp
    @8
    vs
    cS
    cS
    @20
    cvv
    lshpset.s
    cW
    clss
    fvex
    eqeltri
    rabex
    fvmpt
    syl
    syl5eq
end
