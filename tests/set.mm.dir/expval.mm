include "cc.mm"
include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cneg.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "cexp.mm"
include "wa.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "breq2d.mm"
include "simpl.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "seqeq3d.mm"
include "fveq12d.mm"
include "negeqd.mm"
include "oveq2d.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "df-exp.mm"
include "1ex.mm"
include "fvex.mm"
include "ovex.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem expval
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ N e. ZZ ) -> ( A ^ N ) = if ( N = 0 , 1 , if ( 0 < N , ( seq 1 ( x. , ( NN X. { A } ) ) ` N ) , ( 1 / ( seq 1 ( x. , ( NN X. { A } ) ) ` -u N ) ) ) ) )

  proof
    vx
    vy
    cA
    cN
    cc
    cz
    vy
    cv
    #
    cc0
    wceq
    #
    c1
    cc0
    @0
    clt
    wbr
    #
    @0
    cmul
    cn
    vx
    cv
    #
    csn
    #
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    c1
    @0
    cneg
    #
    @6
    cfv
    #
    cdiv
    co
    #
    cif
    #
    cif
    cN
    cc0
    wceq
    #
    c1
    cc0
    cN
    clt
    wbr
    #
    cN
    cmul
    cn
    cA
    csn
    #
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    c1
    cN
    cneg
    #
    @16
    cfv
    #
    cdiv
    co
    #
    cif
    #
    cif
    cexp
    @3
    cA
    wceq
    #
    @0
    cN
    wceq
    #
    wa
    #
    @1
    @12
    @11
    @21
    c1
    @24
    @0
    cN
    cc0
    @22
    @23
    simpr
    #
    eqeq1d
    @24
    @2
    @13
    @7
    @10
    @17
    @20
    @24
    @0
    cN
    cc0
    clt
    @25
    breq2d
    @24
    @0
    cN
    @6
    @16
    @24
    @5
    @15
    cmul
    c1
    @24
    @4
    @14
    cn
    @24
    @3
    cA
    @22
    @23
    simpl
    sneqd
    xpeq2d
    seqeq3d
    #
    @25
    fveq12d
    @24
    @9
    @19
    c1
    cdiv
    @24
    @8
    @18
    @6
    @16
    @26
    @24
    @0
    cN
    @25
    negeqd
    fveq12d
    oveq2d
    ifbieq12d
    ifbieq2d
    vx
    vy
    df-exp
    @12
    c1
    @21
    1ex
    @13
    @17
    @20
    cN
    @16
    fvex
    c1
    @19
    cdiv
    ovex
    ifex
    ifex
    ovmpt2a
end
