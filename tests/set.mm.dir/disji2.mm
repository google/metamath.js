include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "wo.mm"
include "cv.mm"
include "csb.mm"
include "wral.mm"
include "disjors.mm"
include "eqeq1.mm"
include "nfcv.mm"
include "csbhypf.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "eqeq2.mm"
include "ineq2d.mm"
include "rspc2v.mm"
include "syl5bi.mm"
include "impcom.mm"
include "ord.mm"
include "3impia.mm"

theorem disji2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume disji.1: |- ( x = X -> B = C )
  assume disji.2: |- ( x = Y -> B = D )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint X x
  disjoint Y x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D z
  disjoint X y
  disjoint X z
  disjoint Y z
  assert |- ( ( Disj_ x e. A B /\ ( X e. A /\ Y e. A ) /\ X =/= Y ) -> ( C i^i D ) = (/) )

  proof
    vx
    cA
    cB
    wdisj
    #
    cX
    cA
    wcel
    cY
    cA
    wcel
    wa
    #
    cX
    cY
    wne
    #
    cC
    cD
    cin
    #
    c0
    wceq
    #
    @2
    cX
    cY
    wceq
    #
    wn
    @0
    @1
    wa
    #
    @4
    cX
    cY
    df-ne
    @6
    @5
    @4
    @1
    @0
    @5
    @4
    wo
    #
    @0
    vy
    cv
    #
    vz
    cv
    #
    wceq
    #
    vx
    @8
    cB
    csb
    #
    vx
    @9
    cB
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    cA
    wral
    vy
    cA
    wral
    @1
    @7
    vx
    cA
    cB
    vy
    vz
    disjors
    @15
    @7
    cX
    @9
    wceq
    #
    cC
    @12
    cin
    #
    c0
    wceq
    #
    wo
    vy
    vz
    cX
    cY
    cA
    cA
    @8
    cX
    wceq
    #
    @10
    @16
    @14
    @18
    @8
    cX
    @9
    eqeq1
    @19
    @13
    @17
    c0
    @19
    @11
    cC
    @12
    vx
    vy
    cX
    cB
    cC
    vx
    cX
    nfcv
    vx
    cC
    nfcv
    disji.1
    csbhypf
    ineq1d
    eqeq1d
    orbi12d
    @9
    cY
    wceq
    #
    @16
    @5
    @18
    @4
    @9
    cY
    cX
    eqeq2
    @20
    @17
    @3
    c0
    @20
    @12
    cD
    cC
    vx
    vz
    cY
    cB
    cD
    vx
    cY
    nfcv
    vx
    cD
    nfcv
    disji.2
    csbhypf
    ineq2d
    eqeq1d
    orbi12d
    rspc2v
    syl5bi
    impcom
    ord
    syl5bi
    3impia
end
