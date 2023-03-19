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
include "eleq1.mm"
include "opeq1.mm"
include "rdgeq2.mm"
include "syl.mm"
include "id.mm"
include "fveq12d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-finxp.mm"
include "3eqtr4g.mm"

theorem finxpeq2
  let cU: class U
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( M = N -> ( U ^^ M ) = ( U ^^ N ) )

  proof
    cM
    cN
    wceq
    #
    cM
    com
    wcel
    #
    c0
    cM
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    vx
    cv
    #
    cU
    wcel
    wa
    c0
    @3
    cvv
    cU
    cxp
    wcel
    @2
    cuni
    @3
    c1st
    cfv
    cop
    @2
    @3
    cop
    cif
    cif
    cmpt2
    #
    cM
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
    cN
    com
    wcel
    #
    c0
    cN
    @4
    cN
    @5
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
    cU
    cM
    cfinxp
    cU
    cN
    cfinxp
    @0
    @10
    @16
    vy
    @0
    @1
    @11
    @9
    @15
    cM
    cN
    com
    eleq1
    @0
    @8
    @14
    c0
    @0
    cM
    cN
    @7
    @13
    @0
    @6
    @12
    wceq
    @7
    @13
    wceq
    cM
    cN
    @5
    opeq1
    @6
    @12
    @4
    rdgeq2
    syl
    @0
    id
    fveq12d
    eqeq2d
    anbi12d
    abbidv
    vx
    vy
    cU
    vn
    cM
    df-finxp
    vx
    vy
    cU
    vn
    cN
    df-finxp
    3eqtr4g
end
