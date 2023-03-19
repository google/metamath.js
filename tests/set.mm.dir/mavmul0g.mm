include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "co.mm"
include "oveq12.mm"
include "mavmul0.mm"
include "sylan9eq.mm"
include "cdm.mm"
include "csn.mm"
include "cxp.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "eqid.mm"
include "simpr.mm"
include "cfn.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "mvmulfval.mm"
include "dmeqd.mm"
include "cvv.mm"
include "wral.mm"
include "0ex.mm"
include "mptexg.mm"
include "syl.mm"
include "ralrimivva.mm"
include "dmmpt2ga.mm"
include "c1o.mm"
include "id.mm"
include "xpeq12d.mm"
include "0xp.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "fvex.mm"
include "map0e.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "df1o2.mm"
include "oveq2.mm"
include "3eqtrd.mm"
include "elsni.mm"
include "anim12i.mm"
include "con3i.mm"
include "ndmovg.mm"
include "syl2anr.mm"
include "pm2.61ian.mm"

theorem mavmul0g
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume mavmul0.t: |- .x. = ( R maVecMul <. N , N >. )


  assert |- ( ( N = (/) /\ R e. V ) -> ( X .x. Y ) = (/) )

  proof
    cX
    c0
    wceq
    #
    cY
    c0
    wceq
    #
    wa
    #
    cN
    c0
    wceq
    #
    cR
    cV
    wcel
    #
    wa
    #
    cX
    cY
    c.x
    co
    #
    c0
    wceq
    #
    @2
    @5
    @6
    c0
    c0
    c.x
    co
    c0
    cX
    c0
    cY
    c0
    c.x
    oveq12
    cR
    c.x
    cN
    cV
    mavmul0.t
    mavmul0
    sylan9eq
    @5
    c.x
    cdm
    #
    c0
    csn
    #
    @9
    cxp
    #
    wceq
    cX
    @9
    wcel
    #
    cY
    @9
    wcel
    #
    wa
    #
    wn
    @7
    @2
    wn
    @5
    @8
    vi
    vj
    cR
    cbs
    cfv
    #
    cN
    cN
    cxp
    #
    cmap
    co
    #
    @14
    cN
    cmap
    co
    #
    vk
    cN
    cR
    vl
    cN
    vk
    cv
    vl
    cv
    #
    vi
    cv
    #
    co
    @18
    vj
    cv
    #
    cfv
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cmpt
    #
    cmpt2
    #
    cdm
    #
    @16
    @17
    cxp
    #
    @10
    @5
    c.x
    @24
    @5
    vi
    vj
    @14
    cR
    @21
    c.x
    vk
    vl
    cN
    cN
    cV
    mavmul0.t
    @14
    eqid
    @21
    eqid
    @3
    @4
    simpr
    @3
    cN
    cfn
    wcel
    #
    @4
    @3
    @27
    c0
    cfn
    wcel
    0fin
    cN
    c0
    cfn
    eleq1
    mpbiri
    adantr
    #
    @28
    mvmulfval
    dmeqd
    @5
    @23
    cvv
    wcel
    #
    vj
    @17
    wral
    vi
    @16
    wral
    @25
    @26
    wceq
    @5
    @29
    vi
    vj
    @16
    @17
    @5
    @29
    @19
    @16
    wcel
    @20
    @17
    wcel
    wa
    @3
    @29
    @4
    @3
    cN
    cvv
    wcel
    #
    @29
    @3
    @30
    c0
    cvv
    wcel
    0ex
    cN
    c0
    cvv
    eleq1
    mpbiri
    vk
    cN
    @22
    cvv
    mptexg
    syl
    adantr
    adantr
    ralrimivva
    vi
    vj
    @16
    @17
    @23
    @24
    cvv
    @24
    eqid
    dmmpt2ga
    syl
    @5
    @16
    @9
    @17
    @9
    @5
    @16
    c1o
    @9
    @3
    @16
    c1o
    wceq
    @4
    @3
    @16
    @14
    c0
    cmap
    co
    #
    c1o
    @3
    @15
    c0
    @14
    cmap
    @3
    @15
    c0
    c0
    cxp
    c0
    @3
    cN
    c0
    cN
    c0
    @3
    id
    #
    @32
    xpeq12d
    c0
    0xp
    syl6eq
    oveq2d
    @14
    cvv
    wcel
    #
    @31
    c1o
    wceq
    #
    @3
    cR
    cbs
    fvex
    #
    @14
    cvv
    map0e
    #
    mp1i
    eqtrd
    adantr
    df1o2
    syl6eq
    @3
    @4
    @17
    @31
    @9
    cN
    c0
    @14
    cmap
    oveq2
    @4
    @31
    c1o
    @9
    @33
    @34
    @4
    @35
    @36
    mp1i
    df1o2
    syl6eq
    sylan9eq
    xpeq12d
    3eqtrd
    @13
    @2
    @11
    @0
    @12
    @1
    cX
    c0
    elsni
    cY
    c0
    elsni
    anim12i
    con3i
    cX
    cY
    @9
    @9
    c.x
    ndmovg
    syl2anr
    pm2.61ian
end
