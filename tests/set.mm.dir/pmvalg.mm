include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wfun.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "cvv.mm"
include "cpm.mm"
include "co.mm"
include "wceq.mm"
include "wss.mm"
include "ssrab2.mm"
include "xpexg.mm"
include "ancoms.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "wi.mm"
include "elex.mm"
include "xpeq2.mm"
include "pweqd.mm"
include "rabeq.mm"
include "xpeq1.mm"
include "df-pm.mm"
include "ovmpt2g.mm"
include "3expia.mm"
include "syl2an.mm"
include "mpd.mm"

theorem pmvalg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y

  disjoint A f
  disjoint B f
  disjoint x y
  disjoint f x
  disjoint A x
  disjoint f y
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. C /\ B e. D ) -> ( A ^pm B ) = { f e. ~P ( B X. A ) | Fun f } )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    vf
    cv
    wfun
    #
    vf
    cB
    cA
    cxp
    #
    cpw
    #
    crab
    #
    cvv
    wcel
    #
    cA
    cB
    cpm
    co
    @6
    wceq
    #
    @2
    @6
    @5
    wss
    @5
    cvv
    wcel
    #
    @7
    @3
    vf
    @5
    ssrab2
    @2
    @4
    cvv
    wcel
    #
    @9
    @1
    @0
    @10
    cB
    cA
    cD
    cC
    xpexg
    ancoms
    @4
    cvv
    pwexg
    syl
    @6
    @5
    cvv
    ssexg
    sylancr
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @7
    @8
    wi
    @1
    cA
    cC
    elex
    cB
    cD
    elex
    @11
    @12
    @7
    @8
    vx
    vy
    cA
    cB
    cvv
    cvv
    @3
    vf
    vy
    cv
    #
    vx
    cv
    #
    cxp
    #
    cpw
    #
    crab
    #
    @6
    cpm
    @3
    vf
    @13
    cA
    cxp
    #
    cpw
    #
    crab
    #
    cvv
    @14
    cA
    wceq
    #
    @16
    @19
    wceq
    @17
    @20
    wceq
    @21
    @15
    @18
    @14
    cA
    @13
    xpeq2
    pweqd
    @3
    vf
    @16
    @19
    rabeq
    syl
    @13
    cB
    wceq
    #
    @19
    @5
    wceq
    @20
    @6
    wceq
    @22
    @18
    @4
    @13
    cB
    cA
    xpeq1
    pweqd
    @3
    vf
    @19
    @5
    rabeq
    syl
    vx
    vy
    vf
    df-pm
    ovmpt2g
    3expia
    syl2an
    mpd
end
