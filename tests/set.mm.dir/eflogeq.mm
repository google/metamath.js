include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "ce.mm"
include "cfv.mm"
include "wceq.mm"
include "clog.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "cz.mm"
include "wrex.mm"
include "cmin.mm"
include "cdiv.mm"
include "c1.mm"
include "efcl.mm"
include "efne0.mm"
include "logcld.mm"
include "efsub.mm"
include "mpdan.mm"
include "eflog.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "dividd.mm"
include "3eqtrd.mm"
include "wb.mm"
include "subcl.mm"
include "efeq1.mm"
include "syl.mm"
include "mpbid.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "a1i.mm"
include "ine0.mm"
include "2ne0.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "mulne0i.mm"
include "divcan2d.mm"
include "pncan3.mm"
include "mpancom.mm"
include "eqtr2d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "wa.mm"
include "logcl.mm"
include "3adant1.mm"
include "adantr.mm"
include "zcn.mm"
include "adantl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efadd.mm"
include "ef2kpi.mm"
include "oveqan12d.mm"
include "simpl2.mm"
include "mulid1d.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem eflogeq
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let cN: class N

  disjoint A n
  disjoint B n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint k n
  disjoint N k
  disjoint N n
  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( exp ` A ) = B <-> E. n e. ZZ A = ( ( log ` B ) + ( ( _i x. ( 2 x. _pi ) ) x. n ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    ce
    cfv
    #
    cB
    wceq
    #
    cA
    cB
    clog
    cfv
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    vn
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @3
    cA
    @4
    clog
    cfv
    #
    @10
    caddc
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @5
    @13
    @0
    @1
    @17
    @2
    @0
    cA
    @14
    cmin
    co
    #
    @8
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    @14
    @8
    @19
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @17
    @0
    @18
    ce
    cfv
    #
    c1
    wceq
    #
    @20
    @0
    @24
    @4
    @14
    ce
    cfv
    #
    cdiv
    co
    #
    @4
    @4
    cdiv
    co
    c1
    @0
    @14
    cc
    wcel
    #
    @24
    @27
    wceq
    @0
    @4
    cA
    efcl
    #
    cA
    efne0
    #
    logcld
    #
    cA
    @14
    efsub
    mpdan
    @0
    @26
    @4
    @4
    cdiv
    @0
    @4
    cc
    wcel
    @4
    cc0
    wne
    @26
    @4
    wceq
    @29
    @30
    @4
    eflog
    syl2anc
    oveq2d
    @0
    @4
    @29
    @30
    dividd
    3eqtrd
    @0
    @18
    cc
    wcel
    #
    @25
    @20
    wb
    @0
    @28
    @32
    @31
    cA
    @14
    subcl
    mpdan
    #
    @18
    efeq1
    syl
    mpbid
    @0
    @22
    @14
    @18
    caddc
    co
    #
    cA
    @0
    @21
    @18
    @14
    caddc
    @0
    @18
    @8
    @33
    @8
    cc
    wcel
    #
    @0
    ci
    @7
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    #
    mulcli
    #
    a1i
    @8
    cc0
    wne
    @0
    ci
    @7
    ax-icn
    @36
    ine0
    c2
    cpi
    2cn
    picn
    2ne0
    cpi
    pire
    pipos
    gt0ne0ii
    mulne0i
    mulne0i
    a1i
    divcan2d
    oveq2d
    @28
    @0
    @34
    cA
    wceq
    @31
    @14
    cA
    pncan3
    mpancom
    eqtr2d
    @16
    @23
    vn
    @19
    cz
    @9
    @19
    wceq
    #
    @15
    @22
    cA
    @38
    @10
    @21
    @14
    caddc
    @9
    @19
    @8
    cmul
    oveq2
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    3ad2ant1
    @5
    @16
    @12
    vn
    cz
    @5
    @15
    @11
    cA
    @5
    @14
    @6
    @10
    caddc
    @4
    cB
    clog
    fveq2
    oveq1d
    eqeq2d
    rexbidv
    syl5ibcom
    @3
    @12
    @5
    vn
    cz
    @3
    @9
    cz
    wcel
    #
    wa
    #
    @5
    @12
    @11
    ce
    cfv
    #
    cB
    wceq
    @40
    @41
    @6
    ce
    cfv
    #
    @10
    ce
    cfv
    #
    cmul
    co
    #
    cB
    c1
    cmul
    co
    cB
    @40
    @6
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    @41
    @44
    wceq
    @3
    @45
    @39
    @1
    @2
    @45
    @0
    cB
    logcl
    3adant1
    adantr
    @40
    @35
    @9
    cc
    wcel
    #
    @46
    @37
    @39
    @47
    @3
    @9
    zcn
    adantl
    @8
    @9
    mulcl
    sylancr
    @6
    @10
    efadd
    syl2anc
    @3
    @39
    @42
    cB
    @43
    c1
    cmul
    @1
    @2
    @42
    cB
    wceq
    @0
    cB
    eflog
    3adant1
    @9
    ef2kpi
    oveqan12d
    @40
    cB
    @0
    @1
    @2
    @39
    simpl2
    mulid1d
    3eqtrd
    @12
    @4
    @41
    cB
    cA
    @11
    ce
    fveq2
    eqeq1d
    syl5ibrcom
    rexlimdva
    impbid
end
