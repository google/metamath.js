include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "con0.mm"
include "wss.mm"
include "com.mm"
include "wf.mm"
include "wa.mm"
include "wral.mm"
include "wceq.mm"
include "eleq2.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "weq.mm"
include "noel.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "wo.mm"
include "vex.mm"
include "elsuc.mm"
include "suceq.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "peano2b.mm"
include "ffvelrn.mm"
include "sylan2b.mm"
include "ssel.mm"
include "ontr1.mm"
include "expcomd.mm"
include "syl56.mm"
include "impl.mm"
include "adantlr.mm"
include "mpd.mm"
include "imim2d.mm"
include "imp.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "jaod.mm"
include "syl5bi.mm"
include "exp31.mm"
include "com12.mm"
include "finds2.mm"

theorem omsmolem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let vw: setvar w

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint w x
  disjoint F w
  assert |- ( y e. _om -> ( ( ( A C_ On /\ F : _om --> A ) /\ A. x e. _om ( F ` x ) e. ( F ` suc x ) ) -> ( z e. y -> ( F ` z ) e. ( F ` y ) ) ) )

  proof
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @0
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    wcel
    #
    wi
    @0
    c0
    wcel
    #
    @3
    c0
    cF
    cfv
    #
    wcel
    #
    wi
    #
    @0
    vw
    cv
    #
    wcel
    #
    @3
    @10
    cF
    cfv
    #
    wcel
    #
    wi
    #
    @0
    @10
    csuc
    #
    wcel
    #
    @3
    @15
    cF
    cfv
    #
    wcel
    #
    wi
    #
    cA
    con0
    wss
    #
    com
    cA
    cF
    wf
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    #
    @23
    csuc
    #
    cF
    cfv
    #
    wcel
    #
    vx
    com
    wral
    #
    wa
    #
    vy
    vw
    @1
    c0
    wceq
    #
    @2
    @6
    @5
    @8
    @1
    c0
    @0
    eleq2
    @30
    @4
    @7
    @3
    @1
    c0
    cF
    fveq2
    eleq2d
    imbi12d
    vy
    vw
    weq
    #
    @2
    @11
    @5
    @13
    @1
    @10
    @0
    eleq2
    @31
    @4
    @12
    @3
    @1
    @10
    cF
    fveq2
    eleq2d
    imbi12d
    @1
    @15
    wceq
    #
    @2
    @16
    @5
    @18
    @1
    @15
    @0
    eleq2
    @32
    @4
    @17
    @3
    @1
    @15
    cF
    fveq2
    eleq2d
    imbi12d
    @9
    @29
    @6
    @8
    @0
    noel
    pm2.21i
    a1i
    @29
    @10
    com
    wcel
    #
    @14
    @19
    wi
    @29
    @33
    @14
    @19
    @16
    @11
    vz
    vw
    weq
    #
    wo
    @29
    @33
    wa
    #
    @14
    wa
    #
    @18
    @0
    @10
    vz
    vex
    elsuc
    @36
    @11
    @18
    @34
    @35
    @14
    @11
    @18
    wi
    @35
    @13
    @18
    @11
    @35
    @12
    @17
    wcel
    #
    @13
    @18
    wi
    #
    @28
    @33
    @37
    @22
    @27
    @37
    vx
    @10
    com
    vx
    vw
    weq
    #
    @24
    @12
    @26
    @17
    @23
    @10
    cF
    fveq2
    @39
    @25
    @15
    cF
    @23
    @10
    suceq
    fveq2d
    eleq12d
    rspccva
    #
    adantll
    @22
    @33
    @37
    @38
    wi
    #
    @28
    @20
    @21
    @33
    @41
    @21
    @33
    wa
    @17
    cA
    wcel
    #
    @20
    @17
    con0
    wcel
    #
    @41
    @33
    @21
    @15
    com
    wcel
    @42
    @10
    peano2b
    com
    cA
    @15
    cF
    ffvelrn
    sylan2b
    cA
    con0
    @17
    ssel
    @43
    @13
    @37
    @18
    @3
    @12
    @17
    ontr1
    expcomd
    syl56
    impl
    adantlr
    mpd
    imim2d
    imp
    @35
    @34
    @18
    wi
    #
    @14
    @28
    @33
    @44
    @22
    @28
    @33
    wa
    @18
    @34
    @37
    @40
    @34
    @3
    @12
    @17
    @0
    @10
    cF
    fveq2
    eleq1d
    syl5ibrcom
    adantll
    adantr
    jaod
    syl5bi
    exp31
    com12
    finds2
end
