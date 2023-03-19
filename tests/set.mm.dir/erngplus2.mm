include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "co.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "erngplus.mm"
include "3adantr3.mm"
include "fveq2.mm"
include "coeq12d.mm"
include "adantl.mm"
include "simpr3.mm"
include "fvex.mm"
include "coex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem erngplus2
  let cD: class D
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vw: setvar w
  assume erngset.h: |- H = ( LHyp ` K )
  assume erngset.t: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng.p: |- .+ = ( +g ` D )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ F e. T ) ) -> ( ( U .+ V ) ` F ) = ( ( U ` F ) o. ( V ` F ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
    wa
    #
    vf
    cF
    vf
    cv
    #
    cU
    cfv
    #
    @5
    cV
    cfv
    #
    ccom
    #
    cF
    cU
    cfv
    #
    cF
    cV
    cfv
    #
    ccom
    #
    cT
    cU
    cV
    c.pl
    co
    #
    cvv
    @0
    @1
    @2
    @12
    vf
    cT
    @8
    cmpt
    wceq
    @3
    cD
    c.pl
    cT
    cU
    vf
    cE
    cH
    cK
    cV
    cW
    erngset.h
    erngset.t
    erngset.e
    erngset.d
    erng.p
    erngplus
    3adantr3
    @5
    cF
    wceq
    #
    @8
    @11
    wceq
    @4
    @13
    @6
    @9
    @7
    @10
    @5
    cF
    cU
    fveq2
    @5
    cF
    cV
    fveq2
    coeq12d
    adantl
    @0
    @1
    @2
    @3
    simpr3
    @11
    cvv
    wcel
    @4
    @9
    @10
    cF
    cU
    fvex
    cF
    cV
    fvex
    coex
    a1i
    fvmptd
end
