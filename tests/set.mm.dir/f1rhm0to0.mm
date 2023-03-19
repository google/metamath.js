include "crh.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmid.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "eqeq2d.mm"
include "wi.mm"
include "simp2.mm"
include "simp3.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "ring0cl.mm"
include "f1veqaeq.mm"
include "syl12anc.mm"
include "sylbird.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "impbid.mm"

theorem f1rhm0to0
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume f1rhm0to0.a: |- A = ( Base ` R )
  assume f1rhm0to0.b: |- B = ( Base ` S )
  assume f1rhm0to0.n: |- N = ( 0g ` S )
  assume f1rhm0to0.0: |- .0. = ( 0g ` R )


  assert |- ( ( F e. ( R RingHom S ) /\ F : A -1-1-> B /\ X e. A ) -> ( ( F ` X ) = N <-> X = .0. ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    cX
    cA
    wcel
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cN
    wceq
    #
    cX
    c.0
    wceq
    #
    @3
    @5
    @4
    c.0
    cF
    cfv
    #
    wceq
    #
    @6
    @3
    @7
    cN
    @4
    @0
    @1
    @7
    cN
    wceq
    #
    @2
    @0
    cF
    cR
    cS
    cghm
    co
    wcel
    @9
    cR
    cS
    cF
    rhmghm
    cR
    cS
    cF
    c.0
    cN
    f1rhm0to0.0
    f1rhm0to0.n
    ghmid
    syl
    3ad2ant1
    #
    eqeq2d
    @3
    @1
    @2
    c.0
    cA
    wcel
    #
    @8
    @6
    wi
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @0
    @1
    @11
    @2
    @0
    cR
    crg
    wcel
    @11
    cR
    cS
    cF
    rhmrcl1
    cA
    cR
    c.0
    f1rhm0to0.a
    f1rhm0to0.0
    ring0cl
    syl
    3ad2ant1
    cA
    cB
    cX
    c.0
    cF
    f1veqaeq
    syl12anc
    sylbird
    @3
    @6
    @5
    @6
    @3
    @4
    @7
    cN
    cX
    c.0
    cF
    fveq2
    @10
    sylan9eqr
    ex
    impbid
end
