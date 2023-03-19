include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "c3.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cneg.mm"
include "ci.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "ctp.mm"
include "w3a.mm"
include "wss.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "ax-icn.mm"
include "3cn.mm"
include "sqrtcl.mm"
include "ax-mp.mm"
include "mulcli.mm"
include "addcli.mm"
include "halfcl.mm"
include "subcli.mm"
include "3pm3.2i.mm"
include "elexi.mm"
include "ovex.mm"
include "tpss.mm"
include "mpbi.mm"
include "eqsstri.mm"
include "sseli.mm"
include "pm4.71ri.mm"
include "ccxp.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "cn.mm"
include "wb.mm"
include "3nn.mm"
include "cxpeq.mm"
include "mp3an23.mm"
include "w3o.mm"
include "eltpg.mm"
include "eleq2i.mm"
include "3m1e2.mm"
include "2cn.mm"
include "addid2i.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "cz.mm"
include "0z.mm"
include "fztp.mm"
include "eqtri.mm"
include "rexeqi.mm"
include "3ne0.mm"
include "reccli.mm"
include "1cxp.mm"
include "oveq1i.mm"
include "eqeq2i.mm"
include "rexbii.mm"
include "oveq2.mm"
include "divcli.mm"
include "cxpcl.mm"
include "mp2an.mm"
include "exp0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "1t1e1.mm"
include "eqeq2d.mm"
include "id.mm"
include "exp1.mm"
include "mulid2i.mm"
include "1cubrlem.mm"
include "simpli.mm"
include "sqcli.mm"
include "simpri.mm"
include "rextp.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem 1cubr
  let cA: class A
  let cR: class R
  let vn: setvar n
  assume 1cubr.r: |- R = { 1 , ( ( -u 1 + ( _i x. ( sqrt ` 3 ) ) ) / 2 ) , ( ( -u 1 - ( _i x. ( sqrt ` 3 ) ) ) / 2 ) }


  assert |- ( A e. R <-> ( A e. CC /\ ( A ^ 3 ) = 1 ) )

  proof
    cA
    cR
    wcel
    #
    cA
    cc
    wcel
    #
    @0
    wa
    @1
    cA
    c3
    cexp
    co
    c1
    wceq
    #
    wa
    @0
    @1
    cR
    cc
    cA
    cR
    c1
    c1
    cneg
    #
    ci
    c3
    csqrt
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @3
    @5
    cmin
    co
    #
    c2
    cdiv
    co
    #
    ctp
    #
    cc
    1cubr.r
    c1
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    w3a
    @10
    cc
    wss
    @11
    @12
    @13
    ax-1cn
    @6
    cc
    wcel
    @12
    @3
    @5
    neg1cn
    ci
    @4
    ax-icn
    c3
    cc
    wcel
    @4
    cc
    wcel
    3cn
    c3
    sqrtcl
    ax-mp
    mulcli
    #
    addcli
    @6
    halfcl
    ax-mp
    @8
    cc
    wcel
    @13
    @3
    @5
    neg1cn
    @14
    subcli
    @8
    halfcl
    ax-mp
    3pm3.2i
    c1
    @7
    @9
    cc
    c1
    cc
    ax-1cn
    elexi
    @6
    c2
    cdiv
    ovex
    @8
    c2
    cdiv
    ovex
    tpss
    mpbi
    eqsstri
    sseli
    pm4.71ri
    @1
    @2
    @0
    @1
    @2
    cA
    c1
    c1
    c3
    cdiv
    co
    #
    ccxp
    co
    #
    @3
    c2
    c3
    cdiv
    co
    #
    ccxp
    co
    #
    vn
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    vn
    cc0
    c3
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @0
    @1
    c3
    cn
    wcel
    @11
    @2
    @25
    wb
    3nn
    ax-1cn
    cA
    c1
    vn
    c3
    cxpeq
    mp3an23
    @1
    cA
    @10
    wcel
    cA
    c1
    wceq
    #
    cA
    @7
    wceq
    #
    cA
    @9
    wceq
    #
    w3o
    #
    @0
    @25
    cA
    c1
    @7
    @9
    cc
    eltpg
    cR
    @10
    cA
    1cubr.r
    eleq2i
    @25
    @22
    vn
    cc0
    cc0
    c1
    caddc
    co
    #
    cc0
    c2
    caddc
    co
    #
    ctp
    #
    wrex
    cA
    c1
    @20
    cmul
    co
    #
    wceq
    #
    vn
    @32
    wrex
    @29
    @22
    vn
    @24
    @32
    @24
    cc0
    @31
    cfz
    co
    #
    @32
    @23
    @31
    cc0
    cfz
    @23
    c2
    @31
    3m1e2
    c2
    2cn
    addid2i
    #
    eqtr4i
    oveq2i
    cc0
    cz
    wcel
    @35
    @32
    wceq
    0z
    cc0
    fztp
    ax-mp
    eqtri
    rexeqi
    @22
    @34
    vn
    @32
    @21
    @33
    cA
    @16
    c1
    @20
    cmul
    @15
    cc
    wcel
    @16
    c1
    wceq
    c3
    3cn
    3ne0
    reccli
    @15
    1cxp
    ax-mp
    oveq1i
    eqeq2i
    rexbii
    @34
    @26
    @27
    @28
    vn
    cc0
    @30
    @31
    cc0
    cz
    0z
    elexi
    cc0
    c1
    caddc
    ovex
    cc0
    c2
    caddc
    ovex
    @19
    cc0
    wceq
    #
    @33
    c1
    cA
    @37
    @33
    c1
    c1
    cmul
    co
    c1
    @37
    @20
    c1
    c1
    cmul
    @37
    @20
    @18
    cc0
    cexp
    co
    #
    c1
    @19
    cc0
    @18
    cexp
    oveq2
    @18
    cc
    wcel
    #
    @38
    c1
    wceq
    @3
    cc
    wcel
    @17
    cc
    wcel
    @39
    neg1cn
    c2
    c3
    2cn
    3cn
    3ne0
    divcli
    @3
    @17
    cxpcl
    mp2an
    #
    @18
    exp0
    ax-mp
    syl6eq
    oveq2d
    1t1e1
    syl6eq
    eqeq2d
    @19
    @30
    wceq
    #
    @33
    @7
    cA
    @41
    @33
    c1
    @18
    cmul
    co
    #
    @7
    @41
    @20
    @18
    c1
    cmul
    @41
    @20
    @18
    c1
    cexp
    co
    #
    @18
    @41
    @19
    c1
    @18
    cexp
    @41
    @19
    @30
    c1
    @41
    id
    c1
    ax-1cn
    addid2i
    syl6eq
    oveq2d
    @39
    @43
    @18
    wceq
    @40
    @18
    exp1
    ax-mp
    syl6eq
    oveq2d
    @42
    @18
    @7
    @18
    @40
    mulid2i
    @18
    @7
    wceq
    #
    @18
    c2
    cexp
    co
    #
    @9
    wceq
    #
    1cubrlem
    simpli
    eqtri
    syl6eq
    eqeq2d
    @19
    @31
    wceq
    #
    @33
    @9
    cA
    @47
    @33
    c1
    @45
    cmul
    co
    #
    @9
    @47
    @20
    @45
    c1
    cmul
    @47
    @19
    c2
    @18
    cexp
    @47
    @19
    @31
    c2
    @47
    id
    @36
    syl6eq
    oveq2d
    oveq2d
    @48
    @45
    @9
    @45
    @18
    @40
    sqcli
    mulid2i
    @44
    @46
    1cubrlem
    simpri
    eqtri
    syl6eq
    eqeq2d
    rextp
    3bitri
    3bitr4g
    bitr4d
    pm5.32i
    bitr4i
end
