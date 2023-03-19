include "clvec.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "lshpset2N.mm"
include "eleq2d.mm"
include "cvv.mm"
include "elex.mm"
include "adantl.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elabg.mm"
include "pm5.21nd.mm"
include "bitrd.mm"

theorem islshpkrN
  let cD: class D
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vv: setvar v
  assume lshpset2.v: |- V = ( Base ` W )
  assume lshpset2.d: |- D = ( Scalar ` W )
  assume lshpset2.z: |- .0. = ( 0g ` D )
  assume lshpset2.h: |- H = ( LSHyp ` W )
  assume lshpset2.f: |- F = ( LFnl ` W )
  assume lshpset2.k: |- K = ( LKer ` W )

  disjoint F g
  disjoint H g
  disjoint K g
  disjoint V g
  disjoint W g
  disjoint U g
  disjoint g s
  disjoint H s
  disjoint g v
  disjoint K v
  disjoint V v
  disjoint s v
  disjoint W s
  disjoint W v
  disjoint F s
  disjoint K s
  disjoint U s
  disjoint V s
  disjoint .0. s
  assert |- ( W e. LVec -> ( U e. H <-> E. g e. F ( g =/= ( V X. { .0. } ) /\ U = ( K ` g ) ) ) )

  proof
    cW
    clvec
    wcel
    #
    cU
    cH
    wcel
    cU
    vg
    cv
    #
    cV
    c.0
    csn
    cxp
    wne
    #
    vs
    cv
    #
    @1
    cK
    cfv
    #
    wceq
    #
    wa
    #
    vg
    cF
    wrex
    #
    vs
    cab
    #
    wcel
    #
    @2
    cU
    @4
    wceq
    #
    wa
    #
    vg
    cF
    wrex
    #
    @0
    cH
    @8
    cU
    cD
    vg
    cF
    cH
    cK
    cV
    cW
    c.0
    vs
    lshpset2.v
    lshpset2.d
    lshpset2.z
    lshpset2.h
    lshpset2.f
    lshpset2.k
    lshpset2N
    eleq2d
    @0
    @9
    @12
    cU
    cvv
    wcel
    #
    @9
    @13
    @0
    cU
    @8
    elex
    adantl
    @12
    @13
    @0
    @11
    @13
    vg
    cF
    @10
    @13
    @2
    @10
    @13
    @4
    cvv
    wcel
    @1
    cK
    fvex
    cU
    @4
    cvv
    eleq1
    mpbiri
    adantl
    rexlimivw
    adantl
    @7
    @12
    vs
    cU
    cvv
    @3
    cU
    wceq
    #
    @6
    @11
    vg
    cF
    @14
    @5
    @10
    @2
    @3
    cU
    @4
    eqeq1
    anbi2d
    rexbidv
    elabg
    pm5.21nd
    bitrd
end
