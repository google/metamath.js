include "crh.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "cghm.mm"
include "wb.mm"
include "rhmghm.mm"
include "adantr.mm"
include "ghmf1.mm"
include "syl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "adantl.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "3imp.mm"
include "ghmid.mm"
include "3ad2ant1.mm"
include "sylan9eqr.mm"
include "impbid.mm"

theorem f1rhm0to0ALT
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
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
    @0
    @1
    @2
    @5
    @6
    wi
    #
    @0
    @2
    @1
    @7
    @0
    @2
    @1
    @7
    wi
    @0
    @2
    wa
    #
    @1
    vx
    cv
    #
    cF
    cfv
    #
    cN
    wceq
    #
    @9
    c.0
    wceq
    #
    wi
    #
    vx
    cA
    wral
    #
    @7
    @8
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    @1
    @14
    wb
    @0
    @15
    @2
    cR
    cS
    cF
    rhmghm
    #
    adantr
    vx
    cR
    cS
    cN
    cF
    cA
    cB
    c.0
    f1rhm0to0.a
    f1rhm0to0.b
    f1rhm0to0.0
    f1rhm0to0.n
    ghmf1
    syl
    @2
    @14
    @7
    wi
    @0
    @13
    @7
    vx
    cX
    cA
    @9
    cX
    wceq
    #
    @11
    @5
    @12
    @6
    @17
    @10
    @4
    cN
    @9
    cX
    cF
    fveq2
    eqeq1d
    @9
    cX
    c.0
    eqeq1
    imbi12d
    rspcv
    adantl
    sylbid
    ex
    com23
    3imp
    @3
    @6
    @5
    @6
    @3
    @4
    c.0
    cF
    cfv
    #
    cN
    cX
    c.0
    cF
    fveq2
    @0
    @1
    @18
    cN
    wceq
    #
    @2
    @0
    @15
    @19
    @16
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
    sylan9eqr
    ex
    impbid
end
