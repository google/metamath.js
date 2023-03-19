include "cr.mm"
include "crp.mm"
include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmin.mm"
include "cmul.mm"
include "csqrt.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "halfcn.mm"
include "dvcxp1.mm"
include "ax-mp.mm"
include "rpcn.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "oveq2i.mm"
include "cneg.mm"
include "cc0.mm"
include "caddc.mm"
include "1p0e1.mm"
include "ax-1cn.mm"
include "2halves.mm"
include "eqtr4i.mm"
include "wb.mm"
include "0cn.mm"
include "addsubeq4.mm"
include "mp4an.mm"
include "mpbi.mm"
include "df-neg.mm"
include "rpne0.mm"
include "a1i.mm"
include "cxpnegd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wne.mm"
include "wa.mm"
include "2cnne0.mm"
include "rpsqrtcl.mm"
include "rpcnne0d.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "1t1e1.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "3eqtr3i.mm"

theorem dvsqrt
  let vx: setvar x


  assert |- ( RR _D ( x e. RR+ |-> ( sqrt ` x ) ) ) = ( x e. RR+ |-> ( 1 / ( 2 x. ( sqrt ` x ) ) ) )

  proof
    cr
    vx
    crp
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    ccxp
    co
    #
    cmpt
    #
    cdv
    co
    #
    vx
    crp
    @1
    @0
    @1
    c1
    cmin
    co
    #
    ccxp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cr
    vx
    crp
    @0
    csqrt
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    crp
    c1
    c2
    @9
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    @1
    cc
    wcel
    #
    @4
    @8
    wceq
    halfcn
    vx
    @1
    dvcxp1
    ax-mp
    @3
    @10
    cr
    cdv
    vx
    crp
    @2
    @9
    @0
    crp
    wcel
    #
    @0
    cc
    wcel
    @2
    @9
    wceq
    @0
    rpcn
    #
    @0
    cxpsqrt
    syl
    #
    mpteq2ia
    oveq2i
    vx
    crp
    @7
    @12
    @14
    @7
    @1
    c1
    @9
    cdiv
    co
    #
    cmul
    co
    #
    @12
    @14
    @6
    @17
    @1
    cmul
    @14
    @6
    c1
    @2
    cdiv
    co
    #
    @17
    @14
    @6
    @0
    @1
    cneg
    #
    ccxp
    co
    @19
    @5
    @20
    @0
    ccxp
    @5
    cc0
    @1
    cmin
    co
    #
    @20
    c1
    cc0
    caddc
    co
    #
    @1
    @1
    caddc
    co
    #
    wceq
    #
    @5
    @21
    wceq
    #
    @22
    c1
    @23
    1p0e1
    c1
    cc
    wcel
    #
    @23
    c1
    wceq
    ax-1cn
    c1
    2halves
    ax-mp
    eqtr4i
    @26
    cc0
    cc
    wcel
    @13
    @13
    @24
    @25
    wb
    ax-1cn
    0cn
    halfcn
    halfcn
    c1
    cc0
    @1
    @1
    addsubeq4
    mp4an
    mpbi
    @1
    df-neg
    eqtr4i
    oveq2i
    @14
    @0
    @1
    @15
    @0
    rpne0
    @13
    @14
    halfcn
    a1i
    cxpnegd
    syl5eq
    @14
    @2
    @9
    c1
    cdiv
    @16
    oveq2d
    eqtrd
    oveq2d
    @14
    @18
    c1
    c1
    cmul
    co
    #
    @11
    cdiv
    co
    #
    @12
    @14
    @26
    @26
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @9
    cc
    wcel
    @9
    cc0
    wne
    wa
    @18
    @28
    wceq
    @26
    @14
    ax-1cn
    a1i
    #
    @30
    @29
    @14
    2cnne0
    a1i
    @14
    @9
    @0
    rpsqrtcl
    rpcnne0d
    c1
    c1
    c2
    @9
    divmuldiv
    syl22anc
    @27
    c1
    @11
    cdiv
    1t1e1
    oveq1i
    syl6eq
    eqtrd
    mpteq2ia
    3eqtr3i
end
