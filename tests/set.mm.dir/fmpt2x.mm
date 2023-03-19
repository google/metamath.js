include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "wral.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wf.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "raliunxp.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "wa.mm"
include "coprab.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfeq2.mm"
include "nfcv.mm"
include "nfcsb.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "csbeq1a.mm"
include "eleq2d.mm"
include "sylan9bbr.mm"
include "anbi12d.mm"
include "sylan9eqr.mm"
include "eqeq2d.mm"
include "cbvoprab12.mm"
include "df-mpt2.mm"
include "3eqtr4i.mm"
include "mpt2mptx.mm"
include "fmpt.mm"
include "bitr3i.mm"
include "nfel1.mm"
include "nfral.mm"
include "cbvral.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "nfxp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "feq2i.mm"
include "3bitr4i.mm"

theorem fmpt2x
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume fmpt2x.1: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint D x
  disjoint D y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C z
  disjoint D v
  disjoint D w
  disjoint D z
  assert |- ( A. x e. A A. y e. B C e. D <-> F : U_ x e. A ( { x } X. B ) --> D )

  proof
    vx
    vz
    cv
    #
    vy
    vw
    cv
    #
    cC
    csb
    #
    csb
    #
    cD
    wcel
    #
    vw
    vx
    @0
    cB
    csb
    #
    wral
    #
    vz
    cA
    wral
    #
    vz
    cA
    @0
    csn
    #
    @5
    cxp
    #
    ciun
    #
    cD
    cF
    wf
    #
    cC
    cD
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    cD
    cF
    wf
    @7
    vx
    vv
    cv
    #
    c1st
    cfv
    #
    vy
    @18
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    cD
    wcel
    #
    vv
    @10
    wral
    @11
    @23
    @4
    vv
    vz
    vw
    cA
    @5
    @18
    @0
    @1
    cop
    wceq
    #
    @22
    @3
    cD
    @24
    @22
    vx
    @0
    @21
    csb
    @3
    @24
    vx
    @19
    @0
    @21
    @0
    @1
    @18
    vz
    vex
    #
    vw
    vex
    #
    op1std
    csbeq1d
    @24
    vx
    @0
    @21
    @2
    @24
    vy
    @20
    @1
    cC
    @0
    @1
    @18
    @25
    @26
    op2ndd
    csbeq1d
    csbeq2dv
    eqtrd
    #
    eleq1d
    raliunxp
    vv
    @10
    cD
    @22
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    #
    vz
    vw
    cA
    @5
    @3
    cmpt2
    #
    cF
    vv
    @10
    @22
    cmpt
    @14
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @18
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vv
    coprab
    @0
    cA
    wcel
    #
    @1
    @5
    wcel
    #
    wa
    #
    @18
    @3
    wceq
    #
    wa
    #
    vz
    vw
    vv
    coprab
    @28
    @29
    @35
    @40
    vx
    vy
    vv
    vz
    vw
    @35
    vz
    nfv
    @35
    vw
    nfv
    @38
    @39
    vx
    @36
    @37
    vx
    @36
    vx
    nfv
    vx
    vw
    @5
    vx
    @0
    cB
    nfcsb1v
    #
    nfcri
    nfan
    vx
    @18
    @3
    vx
    @0
    @2
    nfcsb1v
    #
    nfeq2
    nfan
    @38
    @39
    vy
    @38
    vy
    nfv
    vy
    @18
    @3
    vy
    vx
    @0
    @2
    vy
    @0
    nfcv
    vy
    @1
    cC
    nfcsb1v
    #
    nfcsb
    nfeq2
    nfan
    @14
    @0
    wceq
    #
    @31
    @1
    wceq
    #
    wa
    #
    @33
    @38
    @34
    @39
    @46
    @30
    @36
    @32
    @37
    @44
    @30
    @36
    wb
    @45
    @14
    @0
    cA
    eleq1
    adantr
    @45
    @32
    @1
    cB
    wcel
    @44
    @37
    @31
    @1
    cB
    eleq1
    @44
    cB
    @5
    @1
    vx
    @0
    cB
    csbeq1a
    #
    eleq2d
    sylan9bbr
    anbi12d
    @46
    cC
    @3
    @18
    @45
    @44
    cC
    @2
    @3
    vy
    @1
    cC
    csbeq1a
    #
    vx
    @0
    @2
    csbeq1a
    #
    sylan9eqr
    eqeq2d
    anbi12d
    cbvoprab12
    vx
    vy
    vv
    cA
    cB
    cC
    df-mpt2
    vz
    vw
    vv
    cA
    @5
    @3
    df-mpt2
    3eqtr4i
    fmpt2x.1
    vz
    vw
    vv
    cA
    @5
    @22
    @3
    @27
    mpt2mptx
    3eqtr4i
    fmpt
    bitr3i
    @13
    @6
    vx
    vz
    cA
    @13
    vz
    nfv
    @4
    vx
    vw
    @5
    @41
    vx
    @3
    cD
    @42
    nfel1
    nfral
    @13
    @2
    cD
    wcel
    #
    vw
    cB
    wral
    @44
    @6
    @12
    @50
    vy
    vw
    cB
    @12
    vw
    nfv
    vy
    @2
    cD
    @43
    nfel1
    @45
    cC
    @2
    cD
    @48
    eleq1d
    cbvral
    @44
    @50
    @4
    vw
    cB
    @5
    @47
    @44
    @2
    @3
    cD
    @49
    eleq1d
    raleqbidv
    syl5bb
    cbvral
    @17
    @10
    cD
    cF
    vx
    vz
    cA
    @16
    @9
    vz
    @16
    nfcv
    vx
    @8
    @5
    vx
    @8
    nfcv
    @41
    nfxp
    @44
    @15
    @8
    cB
    @5
    @14
    @0
    sneq
    @47
    xpeq12d
    cbviun
    feq2i
    3bitr4i
end
