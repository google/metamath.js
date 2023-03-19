include "cc.mm"
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
include "wcel.mm"
include "wceq.mm"
include "halfcn.mm"
include "dvcncxp1.mm"
include "ax-mp.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "oveq2i.mm"
include "cneg.mm"
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
include "logdmn0.mm"
include "a1i.mm"
include "cxpnegd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "1cnd.mm"
include "2cnd.mm"
include "sqrtcld.mm"
include "wne.mm"
include "2ne0.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "sqr00d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "divmuldivd.mm"
include "1t1e1.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "3eqtr3i.mm"

theorem dvcnsqrt
  let vx: setvar x
  let cD: class D
  let vy: setvar y
  let cA: class A
  assume dvcncxp1.d: |- D = ( CC \ ( -oo (,] 0 ) )

  disjoint D x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D y
  assert |- ( CC _D ( x e. D |-> ( sqrt ` x ) ) ) = ( x e. D |-> ( 1 / ( 2 x. ( sqrt ` x ) ) ) )

  proof
    cc
    vx
    cD
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
    cD
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
    cc
    vx
    cD
    @0
    csqrt
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    cD
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
    cD
    dvcncxp1.d
    dvcncxp1
    ax-mp
    @3
    @10
    cc
    cdv
    vx
    cD
    @2
    @9
    @0
    cD
    wcel
    #
    @0
    cc
    wcel
    #
    @2
    @9
    wceq
    cD
    cc
    @0
    cD
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    cc
    dvcncxp1.d
    cc
    @16
    difss
    eqsstri
    sseli
    #
    @0
    cxpsqrt
    syl
    #
    mpteq2ia
    oveq2i
    vx
    cD
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
    @19
    @1
    cmul
    @14
    @6
    c1
    @2
    cdiv
    co
    #
    @19
    @14
    @6
    @0
    @1
    cneg
    #
    ccxp
    co
    @21
    @5
    @22
    @0
    ccxp
    @5
    cc0
    @1
    cmin
    co
    #
    @22
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
    @23
    wceq
    #
    @24
    c1
    @25
    1p0e1
    c1
    cc
    wcel
    #
    @25
    c1
    wceq
    ax-1cn
    c1
    2halves
    ax-mp
    eqtr4i
    @28
    cc0
    cc
    wcel
    @13
    @13
    @26
    @27
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
    @17
    @0
    cD
    dvcncxp1.d
    logdmn0
    #
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
    @18
    oveq2d
    eqtrd
    oveq2d
    @14
    @20
    c1
    c1
    cmul
    co
    #
    @11
    cdiv
    co
    @12
    @14
    c1
    c2
    c1
    @9
    @14
    1cnd
    #
    @14
    2cnd
    @31
    @14
    @0
    @17
    sqrtcld
    c2
    cc0
    wne
    @14
    2ne0
    a1i
    @14
    @0
    cc0
    wne
    @9
    cc0
    wne
    @29
    @14
    @9
    cc0
    @0
    cc0
    @14
    @9
    cc0
    wceq
    #
    @0
    cc0
    wceq
    @14
    @32
    wa
    @0
    @14
    @15
    @32
    @17
    adantr
    @14
    @32
    simpr
    sqr00d
    ex
    necon3d
    mpd
    divmuldivd
    @30
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
