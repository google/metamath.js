include "wcel.mm"
include "wa.mm"
include "co.mm"
include "crh.mm"
include "cringcALTV.mm"
include "cfv.mm"
include "chom.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq12.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "cbs.mm"
include "eqid.mm"
include "srhmsubcALTVlem1.mm"
include "sylan2.mm"
include "ringchomALTV.mm"
include "eqtr4d.mm"

theorem srhmsubcALTVlem2
  let cC: class C
  let cS: class S
  let cU: class U
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume srhmsubcALTV.s: |- A. r e. S r e. Ring
  assume srhmsubcALTV.c: |- C = ( U i^i S )
  assume srhmsubcALTV.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )

  disjoint S r
  disjoint X r
  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint X s
  disjoint Y r
  disjoint Y s
  disjoint k x
  assert |- ( ( U e. V /\ ( X e. C /\ Y e. C ) ) -> ( X J Y ) = ( X ( Hom ` ( RingCatALTV ` U ) ) Y ) )

  proof
    cU
    cV
    wcel
    #
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cJ
    co
    cX
    cY
    crh
    co
    #
    cX
    cY
    cU
    cringcALTV
    cfv
    #
    chom
    cfv
    #
    co
    @4
    vr
    vs
    cX
    cY
    cC
    cC
    vr
    cv
    #
    vs
    cv
    #
    crh
    co
    #
    @5
    cJ
    cvv
    cJ
    vr
    vs
    cC
    cC
    @10
    cmpt2
    wceq
    @4
    srhmsubcALTV.j
    a1i
    @8
    cX
    wceq
    @9
    cY
    wceq
    wa
    @10
    @5
    wceq
    @4
    @8
    cX
    @9
    cY
    crh
    oveq12
    adantl
    @3
    @1
    @0
    @1
    @2
    simpl
    #
    adantl
    @3
    @2
    @0
    @1
    @2
    simpr
    #
    adantl
    @4
    cX
    cY
    crh
    ovexd
    ovmpt2d
    @4
    @6
    cbs
    cfv
    #
    @6
    cU
    @7
    cV
    cX
    cY
    @6
    eqid
    @13
    eqid
    @0
    @3
    simpl
    @7
    eqid
    @3
    @0
    @1
    cX
    @13
    wcel
    @11
    cC
    cS
    cU
    cV
    cX
    vr
    srhmsubcALTV.s
    srhmsubcALTV.c
    srhmsubcALTVlem1
    sylan2
    @3
    @0
    @2
    cY
    @13
    wcel
    @12
    cC
    cS
    cU
    cV
    cY
    vr
    srhmsubcALTV.s
    srhmsubcALTV.c
    srhmsubcALTVlem1
    sylan2
    ringchomALTV
    eqtr4d
end
