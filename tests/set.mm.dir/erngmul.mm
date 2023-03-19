include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "erngfmul.mm"
include "oveqd.mm"
include "cvv.mm"
include "wceq.mm"
include "coexg.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"
include "sylan9eq.mm"

theorem erngmul
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
  assume erngset.h: |- H = ( LHyp ` K )
  assume erngset.t: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng.m: |- .x. = ( .r ` D )


  assert |- ( ( ( K e. X /\ W e. H ) /\ ( U e. E /\ V e. E ) ) -> ( U .x. V ) = ( U o. V ) )

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
    vs
    cv
    #
    vt
    cv
    #
    ccom
    #
    cmpt2
    #
    co
    #
    cU
    cV
    ccom
    #
    @0
    c.x
    @6
    cU
    cV
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
    erngset.h
    erngset.t
    erngset.e
    erngset.d
    erng.m
    erngfmul
    oveqd
    @1
    @2
    @8
    cvv
    wcel
    @7
    @8
    wceq
    cU
    cV
    cE
    cE
    coexg
    vs
    vt
    cU
    cV
    cE
    cE
    @5
    @8
    @6
    cU
    @4
    ccom
    cvv
    @3
    cU
    @4
    coeq1
    @4
    cV
    cU
    coeq2
    @6
    eqid
    ovmpt2g
    mpd3an3
    sylan9eq
end
