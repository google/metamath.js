include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "wo.mm"
include "weq.mm"
include "csb.mm"
include "wral.mm"
include "disjors.mm"
include "equequ1.mm"
include "csbeq1.mm"
include "csbid.mm"
include "syl6eq.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "eqeq2.mm"
include "nfcv.mm"
include "csbhypf.mm"
include "ineq2d.mm"
include "rspc2v.mm"
include "syl5bi.mm"
include "impcom.mm"
include "ord.mm"
include "3impia.mm"

theorem disji2f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume disjif.1: |- F/_ x C
  assume disjif.2: |- ( x = Y -> B = C )

  disjoint A x
  disjoint Y x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint Y z
  assert |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\ x =/= Y ) -> ( B i^i C ) = (/) )

  proof
    vx
    cA
    cB
    wdisj
    #
    vx
    cv
    #
    cA
    wcel
    cY
    cA
    wcel
    wa
    #
    @1
    cY
    wne
    #
    cB
    cC
    cin
    #
    c0
    wceq
    #
    @3
    @1
    cY
    wceq
    #
    wn
    @0
    @2
    wa
    #
    @5
    @1
    cY
    df-ne
    @7
    @6
    @5
    @2
    @0
    @6
    @5
    wo
    #
    @0
    vy
    vz
    weq
    #
    vx
    vy
    cv
    #
    cB
    csb
    #
    vx
    vz
    cv
    #
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
    @2
    @8
    vx
    cA
    cB
    vy
    vz
    disjors
    @16
    @8
    vx
    vz
    weq
    #
    cB
    @13
    cin
    #
    c0
    wceq
    #
    wo
    vy
    vz
    @1
    cY
    cA
    cA
    vy
    vx
    weq
    #
    @9
    @17
    @15
    @19
    vy
    vx
    vz
    equequ1
    @20
    @14
    @18
    c0
    @20
    @11
    cB
    @13
    @20
    @11
    vx
    @1
    cB
    csb
    cB
    vx
    @10
    @1
    cB
    csbeq1
    vx
    cB
    csbid
    syl6eq
    ineq1d
    eqeq1d
    orbi12d
    @12
    cY
    wceq
    #
    @17
    @6
    @19
    @5
    @12
    cY
    @1
    eqeq2
    @21
    @18
    @4
    c0
    @21
    @13
    cC
    cB
    vx
    vz
    cY
    cB
    cC
    vx
    cY
    nfcv
    disjif.1
    disjif.2
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
