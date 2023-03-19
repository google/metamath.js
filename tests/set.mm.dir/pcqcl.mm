include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "cpc.mm"
include "simprl.mm"
include "elq.mm"
include "sylib.mm"
include "wi.mm"
include "nncn.mm"
include "nnne0.mm"
include "div0d.mm"
include "ad2antll.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "an32.mm"
include "w3a.mm"
include "cmin.mm"
include "pcdiv.mm"
include "pczcl.mm"
include "nn0zd.mm"
include "3adant3.mm"
include "nnz.mm"
include "jca.mm"
include "sylan2.mm"
include "3adant2.mm"
include "zsubcld.mm"
include "eqeltrd.mm"
include "3expb.mm"
include "sylan2b.mm"
include "expr.mm"
include "syld.mm"
include "neeq1.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "com23.mm"
include "impancom.mm"
include "adantrl.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem pcqcl
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ ( N e. QQ /\ N =/= 0 ) ) -> ( P pCnt N ) e. ZZ )

  proof
    cP
    cprime
    wcel
    #
    cN
    cq
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    wa
    #
    cN
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    cP
    cN
    cpc
    co
    #
    cz
    wcel
    #
    @3
    @1
    @8
    @0
    @1
    @2
    simprl
    vx
    vy
    cN
    elq
    sylib
    @3
    @7
    @10
    vx
    vy
    cz
    cn
    @0
    @2
    @4
    cz
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    @7
    @10
    wi
    #
    wi
    @1
    @0
    @13
    @2
    @14
    @0
    @13
    wa
    #
    @7
    @2
    @10
    @15
    @2
    @10
    wi
    @7
    @6
    cc0
    wne
    #
    cP
    @6
    cpc
    co
    #
    cz
    wcel
    #
    wi
    @15
    @16
    @4
    cc0
    wne
    #
    @18
    @15
    @4
    cc0
    @6
    cc0
    @15
    @6
    cc0
    wceq
    @4
    cc0
    wceq
    #
    cc0
    @5
    cdiv
    co
    #
    cc0
    wceq
    #
    @12
    @22
    @0
    @11
    @12
    @5
    @5
    nncn
    @5
    nnne0
    #
    div0d
    ad2antll
    @20
    @6
    @21
    cc0
    @4
    cc0
    @5
    cdiv
    oveq1
    eqeq1d
    syl5ibrcom
    necon3d
    @0
    @13
    @19
    @18
    @13
    @19
    wa
    @0
    @11
    @19
    wa
    #
    @12
    wa
    @18
    @11
    @12
    @19
    an32
    @0
    @24
    @12
    @18
    @0
    @24
    @12
    w3a
    #
    @17
    cP
    @4
    cpc
    co
    #
    cP
    @5
    cpc
    co
    #
    cmin
    co
    cz
    @4
    @5
    cP
    pcdiv
    @25
    @26
    @27
    @0
    @24
    @26
    cz
    wcel
    @12
    @0
    @24
    wa
    @26
    cP
    @4
    pczcl
    nn0zd
    3adant3
    @0
    @12
    @27
    cz
    wcel
    #
    @24
    @12
    @0
    @5
    cz
    wcel
    #
    @5
    cc0
    wne
    #
    wa
    #
    @28
    @12
    @29
    @30
    @5
    nnz
    @23
    jca
    @0
    @31
    wa
    @27
    cP
    @5
    pczcl
    nn0zd
    sylan2
    3adant2
    zsubcld
    eqeltrd
    3expb
    sylan2b
    expr
    syld
    @7
    @2
    @16
    @10
    @18
    cN
    @6
    cc0
    neeq1
    @7
    @9
    @17
    cz
    cN
    @6
    cP
    cpc
    oveq2
    eleq1d
    imbi12d
    syl5ibrcom
    com23
    impancom
    adantrl
    rexlimdvv
    mpd
end
