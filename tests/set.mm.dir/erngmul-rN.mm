include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "wceq.mm"
include "erngfmul-rN.mm"
include "adantr.mm"
include "oveqd.mm"
include "cvv.mm"
include "coexg.mm"
include "ancoms.mm"
include "coeq2.mm"
include "coeq1.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem erngmul-rN
  let cD: class D
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  assume erngset.h-r: |- H = ( LHyp ` K )
  assume erngset.t-r: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e-r: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d-r: |- D = ( ( EDRingR ` K ) ` W )
  assume erng.m-r: |- .x. = ( .r ` D )


  assert |- ( ( ( K e. X /\ W e. H ) /\ ( U e. E /\ V e. E ) ) -> ( U .x. V ) = ( V o. U ) )

  proof
    cK
    cX
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
    wa
    #
    wa
    #
    cU
    cV
    c.x
    co
    cU
    cV
    vs
    vt
    cE
    cE
    vt
    cv
    #
    vs
    cv
    #
    ccom
    #
    cmpt2
    #
    co
    #
    cV
    cU
    ccom
    #
    @4
    c.x
    @8
    cU
    cV
    @0
    c.x
    @8
    wceq
    @3
    vt
    cD
    cT
    c.x
    cE
    cH
    cK
    cX
    cW
    vs
    erngset.h-r
    erngset.t-r
    erngset.e-r
    erngset.d-r
    erng.m-r
    erngfmul-rN
    adantr
    oveqd
    @3
    @9
    @10
    wceq
    #
    @0
    @1
    @2
    @10
    cvv
    wcel
    #
    @11
    @2
    @1
    @12
    cV
    cU
    cE
    cE
    coexg
    ancoms
    vs
    vt
    cU
    cV
    cE
    cE
    @7
    @10
    @8
    @5
    cU
    ccom
    cvv
    @6
    cU
    @5
    coeq2
    @5
    cV
    cU
    coeq1
    @8
    eqid
    ovmpt2g
    mpd3an3
    adantl
    eqtrd
end
