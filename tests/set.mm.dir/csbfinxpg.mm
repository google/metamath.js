include "wcel.mm"
include "cfinxp.mm"
include "csb.mm"
include "com.mm"
include "c0.mm"
include "cvv.mm"
include "cv.mm"
include "c1o.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cif.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cab.mm"
include "df-finxp.mm"
include "csbeq2i.mm"
include "wsbc.mm"
include "sbcan.mm"
include "sbcel1g.mm"
include "sbceq2g.mm"
include "csbfv12.mm"
include "csbrdgg.mm"
include "csbmpt22g.mm"
include "csbconstg.mm"
include "csbif.mm"
include "sbcg.mm"
include "sbcel12.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "csbxp.mm"
include "xpeq1d.mm"
include "syl5eq.mm"
include "eleq12d.mm"
include "ifbieq12d.mm"
include "mpt2eq123dv.mm"
include "eqtrd.mm"
include "csbopg.mm"
include "opeq2d.mm"
include "rdgeq12.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "bitrd.mm"
include "abbidv.mm"
include "csbab.mm"
include "3eqtr4g.mm"

theorem csbfinxpg
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z

  disjoint N x
  disjoint A n
  disjoint A y
  disjoint A z
  disjoint n y
  disjoint n z
  disjoint y z
  disjoint N n
  disjoint N y
  disjoint N z
  disjoint n x
  disjoint x y
  disjoint x z
  disjoint U n
  disjoint U y
  disjoint U z
  disjoint V n
  disjoint V y
  disjoint V z
  assert |- ( A e. V -> [_ A / x ]_ ( U ^^ N ) = ( [_ A / x ]_ U ^^ [_ A / x ]_ N ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cU
    cN
    cfinxp
    #
    csb
    vx
    cA
    cN
    com
    wcel
    #
    c0
    cN
    vn
    vz
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    #
    vz
    cv
    #
    cU
    wcel
    #
    wa
    #
    c0
    @5
    cvv
    cU
    cxp
    #
    wcel
    #
    @3
    cuni
    @5
    c1st
    cfv
    cop
    #
    @3
    @5
    cop
    #
    cif
    #
    cif
    #
    cmpt2
    #
    cN
    vy
    cv
    #
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cab
    #
    csb
    #
    vx
    cA
    cU
    csb
    #
    vx
    cA
    cN
    csb
    #
    cfinxp
    #
    vx
    cA
    @1
    @21
    vz
    vy
    cU
    vn
    cN
    df-finxp
    csbeq2i
    @0
    @20
    vx
    cA
    wsbc
    #
    vy
    cab
    @24
    com
    wcel
    #
    c0
    @24
    vn
    vz
    com
    cvv
    @4
    @5
    @23
    wcel
    #
    wa
    #
    c0
    @5
    cvv
    @23
    cxp
    #
    wcel
    #
    @10
    @11
    cif
    #
    cif
    #
    cmpt2
    #
    @24
    @15
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cab
    @22
    @25
    @0
    @26
    @39
    vy
    @26
    @2
    vx
    cA
    wsbc
    #
    @19
    vx
    cA
    wsbc
    #
    wa
    @0
    @39
    @2
    @19
    vx
    cA
    sbcan
    @0
    @40
    @27
    @41
    @38
    vx
    cA
    cN
    com
    cV
    sbcel1g
    @0
    @41
    c0
    vx
    cA
    @18
    csb
    #
    wceq
    @38
    vx
    cA
    c0
    @18
    cV
    sbceq2g
    @0
    @42
    @37
    c0
    @0
    @42
    @24
    vx
    cA
    @17
    csb
    #
    cfv
    @37
    vx
    cA
    cN
    @17
    csbfv12
    @0
    @24
    @43
    @36
    @0
    @43
    vx
    cA
    @14
    csb
    #
    vx
    cA
    @16
    csb
    #
    crdg
    #
    @36
    vx
    cA
    @14
    @16
    cV
    csbrdgg
    @0
    @44
    @34
    wceq
    @45
    @35
    wceq
    @46
    @36
    wceq
    @0
    @44
    vn
    vz
    vx
    cA
    com
    csb
    #
    vx
    cA
    cvv
    csb
    #
    vx
    cA
    @13
    csb
    #
    cmpt2
    @34
    vx
    vn
    vz
    cA
    @13
    cV
    com
    cvv
    csbmpt22g
    @0
    vn
    vz
    @47
    @48
    @49
    com
    cvv
    @33
    vx
    cA
    com
    cV
    csbconstg
    vx
    cA
    cvv
    cV
    csbconstg
    #
    @0
    @49
    @7
    vx
    cA
    wsbc
    #
    vx
    cA
    c0
    csb
    #
    vx
    cA
    @12
    csb
    #
    cif
    @33
    @7
    vx
    cA
    c0
    @12
    csbif
    @0
    @51
    @29
    @52
    @53
    c0
    @32
    @51
    @4
    vx
    cA
    wsbc
    #
    @6
    vx
    cA
    wsbc
    #
    wa
    @0
    @29
    @4
    @6
    vx
    cA
    sbcan
    @0
    @54
    @4
    @55
    @28
    @4
    vx
    cA
    cV
    sbcg
    @55
    vx
    cA
    @5
    csb
    #
    @23
    wcel
    @0
    @28
    vx
    cA
    @5
    cU
    sbcel12
    @0
    @56
    @5
    @23
    vx
    cA
    @5
    cV
    csbconstg
    #
    eleq1d
    syl5bb
    anbi12d
    syl5bb
    vx
    cA
    c0
    cV
    csbconstg
    @0
    @53
    @9
    vx
    cA
    wsbc
    #
    vx
    cA
    @10
    csb
    #
    vx
    cA
    @11
    csb
    #
    cif
    @32
    @9
    vx
    cA
    @10
    @11
    csbif
    @0
    @58
    @31
    @59
    @60
    @10
    @11
    @58
    @56
    vx
    cA
    @8
    csb
    #
    wcel
    @0
    @31
    vx
    cA
    @5
    @8
    sbcel12
    @0
    @56
    @5
    @61
    @30
    @57
    @0
    @61
    @48
    @23
    cxp
    @30
    vx
    cA
    cvv
    cU
    csbxp
    @0
    @48
    cvv
    @23
    @50
    xpeq1d
    syl5eq
    eleq12d
    syl5bb
    vx
    cA
    @10
    cV
    csbconstg
    vx
    cA
    @11
    cV
    csbconstg
    ifbieq12d
    syl5eq
    ifbieq12d
    syl5eq
    mpt2eq123dv
    eqtrd
    @0
    @45
    @24
    vx
    cA
    @15
    csb
    #
    cop
    @35
    vx
    cA
    cN
    @15
    cV
    csbopg
    @0
    @62
    @15
    @24
    vx
    cA
    @15
    cV
    csbconstg
    opeq2d
    eqtrd
    @45
    @35
    @44
    @34
    rdgeq12
    syl2anc
    eqtrd
    fveq1d
    syl5eq
    eqeq2d
    bitrd
    anbi12d
    syl5bb
    abbidv
    @20
    vx
    vy
    cA
    csbab
    vz
    vy
    @23
    vn
    @24
    df-finxp
    3eqtr4g
    syl5eq
end
