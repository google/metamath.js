include "wss.mm"
include "wn.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wex.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "c0.mm"
include "neq0.mm"
include "ssdif0.mm"
include "xchnxbir.mm"
include "cdiv.mm"
include "co.mm"
include "csm.mm"
include "wa.mm"
include "cc.mm"
include "wi.mm"
include "chil.mm"
include "cr.mm"
include "eldifi.mm"
include "cheli.mm"
include "normcl.mm"
include "3syl.mm"
include "cc0.mm"
include "c0v.mm"
include "cch.mm"
include "ch0.mm"
include "ax-mp.mm"
include "eldifn.mm"
include "mt2.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "con2i.mm"
include "wb.mm"
include "norm-i.mm"
include "mtbird.mm"
include "neqned.mm"
include "rereccld.mm"
include "recnd.mm"
include "csh.mm"
include "chshii.mm"
include "shmulcl.mm"
include "mp3an1.mm"
include "ex.mm"
include "syl.mm"
include "cmul.mm"
include "recidd.mm"
include "oveq1d.mm"
include "ax-hvmulass.mm"
include "syl3anc.mm"
include "ax-hvmulid.mm"
include "3eqtr3d.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "con3d.mm"
include "anim12d.mm"
include "eldif.mm"
include "3imtr4g.mm"
include "pm2.43i.mm"
include "cabs.mm"
include "norm-iii.mm"
include "syl2anc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wne.mm"
include "necon2ai.mm"
include "normgt0.mm"
include "mpbid.mm"
include "1re.mm"
include "0le1.mm"
include "divge0.mm"
include "mpanl12.mm"
include "absidd.mm"
include "recid2d.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem strlem1
  let vu: setvar u
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume strlem1.1: |- A e. CH
  assume strlem1.2: |- B e. CH

  disjoint A u
  disjoint B u
  disjoint u x
  disjoint A x
  disjoint B x
  assert |- ( -. A C_ B -> E. u e. ( A \ B ) ( normh ` u ) = 1 )

  proof
    cA
    cB
    wss
    #
    wn
    vx
    cv
    #
    cA
    cB
    cdif
    #
    wcel
    #
    vx
    wex
    #
    vu
    cv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    vu
    @2
    wrex
    #
    @2
    c0
    wceq
    @4
    @0
    vx
    @2
    neq0
    cA
    cB
    ssdif0
    xchnxbir
    @3
    @8
    vx
    @3
    c1
    @1
    cno
    cfv
    #
    cdiv
    co
    #
    @1
    csm
    co
    #
    @2
    wcel
    #
    @11
    cno
    cfv
    #
    c1
    wceq
    #
    @8
    @3
    @12
    @3
    @1
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    wn
    #
    wa
    @11
    cA
    wcel
    #
    @11
    cB
    wcel
    #
    wn
    #
    wa
    @3
    @12
    @3
    @15
    @18
    @17
    @20
    @3
    @10
    cc
    wcel
    #
    @15
    @18
    wi
    @3
    @10
    @3
    @9
    @3
    @15
    @1
    chil
    wcel
    #
    @9
    cr
    wcel
    #
    @1
    cA
    cB
    eldifi
    #
    @1
    cA
    strlem1.1
    cheli
    #
    @1
    normcl
    3syl
    #
    @3
    @9
    cc0
    @3
    @9
    cc0
    wceq
    #
    @1
    c0v
    wceq
    #
    @28
    @3
    @28
    @3
    c0v
    @2
    wcel
    #
    @29
    c0v
    cB
    wcel
    #
    cB
    cch
    wcel
    @30
    strlem1.2
    cB
    ch0
    ax-mp
    c0v
    cA
    cB
    eldifn
    mt2
    @1
    c0v
    @2
    eleq1
    mtbiri
    #
    con2i
    @3
    @15
    @22
    @27
    @28
    wb
    @24
    @25
    @1
    norm-i
    3syl
    mtbird
    neqned
    #
    rereccld
    #
    recnd
    #
    @21
    @15
    @18
    cA
    csh
    wcel
    @21
    @15
    @18
    cA
    strlem1.1
    chshii
    @10
    @1
    cA
    shmulcl
    mp3an1
    ex
    syl
    @3
    @19
    @16
    @3
    @19
    @9
    @11
    csm
    co
    #
    cB
    wcel
    #
    @16
    @3
    @9
    cc
    wcel
    #
    @19
    @36
    wi
    @3
    @9
    @26
    recnd
    #
    @37
    @19
    @36
    cB
    csh
    wcel
    @37
    @19
    @36
    cB
    strlem1.2
    chshii
    @9
    @11
    cB
    shmulcl
    mp3an1
    ex
    syl
    @3
    @35
    @1
    cB
    @3
    @9
    @10
    cmul
    co
    #
    @1
    csm
    co
    #
    c1
    @1
    csm
    co
    #
    @35
    @1
    @3
    @39
    c1
    @1
    csm
    @3
    @9
    @38
    @32
    recidd
    oveq1d
    @3
    @37
    @21
    @22
    @40
    @35
    wceq
    @38
    @34
    @3
    @15
    @22
    @24
    @25
    syl
    #
    @9
    @10
    @1
    ax-hvmulass
    syl3anc
    @3
    @15
    @22
    @41
    @1
    wceq
    @24
    @25
    @1
    ax-hvmulid
    3syl
    3eqtr3d
    eleq1d
    sylibd
    con3d
    anim12d
    @1
    cA
    cB
    eldif
    @11
    cA
    cB
    eldif
    3imtr4g
    pm2.43i
    @3
    @13
    @10
    cabs
    cfv
    #
    @9
    cmul
    co
    #
    @10
    @9
    cmul
    co
    c1
    @3
    @21
    @22
    @13
    @44
    wceq
    @34
    @42
    @10
    @1
    norm-iii
    syl2anc
    @3
    @43
    @10
    @9
    cmul
    @3
    @10
    @33
    @3
    @23
    cc0
    @9
    clt
    wbr
    #
    cc0
    @10
    cle
    wbr
    #
    @26
    @3
    @1
    c0v
    wne
    #
    @45
    @3
    @1
    c0v
    @31
    necon2ai
    @3
    @15
    @22
    @47
    @45
    wb
    @24
    @25
    @1
    normgt0
    3syl
    mpbid
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @23
    @45
    wa
    @46
    1re
    0le1
    c1
    @9
    divge0
    mpanl12
    syl2anc
    absidd
    oveq1d
    @3
    @9
    @38
    @32
    recid2d
    3eqtrd
    @7
    @14
    vu
    @11
    @2
    @5
    @11
    wceq
    @6
    @13
    c1
    @5
    @11
    cno
    fveq2
    eqeq1d
    rspcev
    syl2anc
    exlimiv
    sylbi
end
