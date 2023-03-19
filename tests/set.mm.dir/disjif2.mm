include "wcel.mm"
include "wa.mm"
include "wdisj.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "inelcm.mm"
include "wo.mm"
include "weq.mm"
include "csb.mm"
include "wral.mm"
include "disjorsf.mm"
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
include "necon1ad.mm"
include "3impia.mm"
include "syl3an3.mm"

theorem disjif2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  assume disjif2.1: |- F/_ x A
  assume disjif2.2: |- F/_ x C
  assume disjif2.3: |- ( x = Y -> B = C )

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
  assert |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\ ( Z e. B /\ Z e. C ) ) -> x = Y )

  proof
    cZ
    cB
    wcel
    cZ
    cC
    wcel
    wa
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
    cB
    cC
    cin
    #
    c0
    wne
    #
    @1
    cY
    wceq
    #
    cZ
    cB
    cC
    inelcm
    @0
    @2
    @4
    @5
    @0
    @2
    wa
    #
    @5
    @3
    c0
    @6
    @5
    @3
    c0
    wceq
    #
    @2
    @0
    @5
    @7
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
    disjif2.1
    disjorsf
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
    @5
    @19
    @7
    @12
    cY
    @1
    eqeq2
    @21
    @18
    @3
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
    disjif2.2
    disjif2.3
    csbhypf
    ineq2d
    eqeq1d
    orbi12d
    rspc2v
    syl5bi
    impcom
    ord
    necon1ad
    3impia
    syl3an3
end
