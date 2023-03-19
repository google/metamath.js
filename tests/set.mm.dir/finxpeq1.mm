include "wceq.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "cvv.mm"
include "cv.mm"
include "c1o.mm"
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
include "cfinxp.mm"
include "eleq2.mm"
include "anbi2d.mm"
include "xpeq2.mm"
include "eleq2d.mm"
include "ifbid.mm"
include "ifbieq2d.mm"
include "mpt2eq3dv.mm"
include "rdgeq1.mm"
include "syl.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "abbidv.mm"
include "df-finxp.mm"
include "3eqtr4g.mm"

theorem finxpeq1
  let cU: class U
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( U = V -> ( U ^^ N ) = ( V ^^ N ) )

  proof
    cU
    cV
    wceq
    #
    cN
    com
    wcel
    #
    c0
    cN
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    #
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    c0
    @4
    cvv
    cU
    cxp
    #
    wcel
    #
    @2
    cuni
    @4
    c1st
    cfv
    cop
    #
    @2
    @4
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
    @1
    c0
    cN
    vn
    vx
    com
    cvv
    @3
    @4
    cV
    wcel
    #
    wa
    #
    c0
    @4
    cvv
    cV
    cxp
    #
    wcel
    #
    @9
    @10
    cif
    #
    cif
    #
    cmpt2
    #
    @14
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
    cU
    cN
    cfinxp
    cV
    cN
    cfinxp
    @0
    @18
    @29
    vy
    @0
    @17
    @28
    @1
    @0
    @16
    @27
    c0
    @0
    cN
    @15
    @26
    @0
    @13
    @25
    wceq
    @15
    @26
    wceq
    @0
    vn
    vx
    com
    cvv
    @12
    @24
    @0
    @6
    @20
    @11
    @23
    c0
    @0
    @5
    @19
    @3
    cU
    cV
    @4
    eleq2
    anbi2d
    @0
    @8
    @22
    @9
    @10
    @0
    @7
    @21
    @4
    cU
    cV
    cvv
    xpeq2
    eleq2d
    ifbid
    ifbieq2d
    mpt2eq3dv
    @14
    @13
    @25
    rdgeq1
    syl
    fveq1d
    eqeq2d
    anbi2d
    abbidv
    vx
    vy
    cU
    vn
    cN
    df-finxp
    vx
    vy
    cV
    vn
    cN
    df-finxp
    3eqtr4g
end
