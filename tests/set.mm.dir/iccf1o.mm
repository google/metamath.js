include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cdiv.mm"
include "wa.mm"
include "cle.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "adantl.mm"
include "recnd.mm"
include "simpl2.mm"
include "mulcld.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "simpl1.mm"
include "addcomd.mm"
include "lincmb01cmp.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "wb.mm"
include "elicc2.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simp1d.mm"
include "eqid.mm"
include "iccshftl.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "resubcld.mm"
include "crp.mm"
include "difrp.mm"
include "biimp3a.mm"
include "adantr.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan1d.mm"
include "mul02d.mm"
include "subidd.mm"
include "eqtr4d.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "3eltr4d.mm"
include "0red.mm"
include "1red.mm"
include "rerpdivcld.mm"
include "iccdil.mm"
include "mpbird.mm"
include "wceq.mm"
include "eqcom.mm"
include "adantrl.mm"
include "adantrr.mm"
include "wne.mm"
include "divmul3d.mm"
include "syl5bb.mm"
include "remulcld.mm"
include "subadd2d.mm"
include "syl6bb.mm"
include "subadd23d.mm"
include "subdid.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "subdird.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "eqeq2d.mm"
include "3bitrd.mm"
include "f1ocnv2d.mm"

theorem iccf1o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  assume iccf1o.1: |- F = ( x e. ( 0 [,] 1 ) |-> ( ( x x. B ) + ( ( 1 - x ) x. A ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. RR /\ B e. RR /\ A < B ) -> ( F : ( 0 [,] 1 ) -1-1-onto-> ( A [,] B ) /\ `' F = ( y e. ( A [,] B ) |-> ( ( y - A ) / ( B - A ) ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    cA
    cB
    cicc
    co
    #
    vx
    cv
    #
    cB
    cmul
    co
    #
    c1
    @6
    cmin
    co
    #
    cA
    cmul
    co
    #
    caddc
    co
    #
    vy
    cv
    #
    cA
    cmin
    co
    #
    cB
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cF
    iccf1o.1
    @3
    @6
    @4
    wcel
    #
    wa
    #
    @10
    @9
    @7
    caddc
    co
    @5
    @16
    @7
    @9
    @16
    @6
    cB
    @16
    @6
    @15
    @6
    cr
    wcel
    #
    @3
    @15
    @17
    cc0
    @6
    cle
    wbr
    @6
    c1
    cle
    wbr
    cc0
    c1
    @6
    0re
    1re
    elicc2i
    simp1bi
    adantl
    #
    recnd
    #
    @16
    cB
    @0
    @1
    @2
    @15
    simpl2
    #
    recnd
    #
    mulcld
    #
    @16
    @8
    cA
    @16
    c1
    cc
    wcel
    @6
    cc
    wcel
    #
    @8
    cc
    wcel
    ax-1cn
    @19
    c1
    @6
    subcl
    sylancr
    @16
    cA
    @0
    @1
    @2
    @15
    simpl1
    #
    recnd
    #
    mulcld
    addcomd
    cA
    cB
    @6
    lincmb01cmp
    eqeltrd
    @3
    @11
    @5
    wcel
    #
    wa
    #
    @14
    @4
    wcel
    #
    @14
    @13
    cmul
    co
    #
    cc0
    @13
    cmul
    co
    #
    c1
    @13
    cmul
    co
    #
    cicc
    co
    #
    wcel
    #
    @27
    @12
    cA
    cA
    cmin
    co
    #
    @13
    cicc
    co
    #
    @29
    @32
    @27
    @26
    @12
    @35
    wcel
    #
    @3
    @26
    simpr
    @27
    @0
    @1
    @11
    cr
    wcel
    #
    @0
    @26
    @36
    wb
    @0
    @1
    @2
    @26
    simpl1
    #
    @0
    @1
    @2
    @26
    simpl2
    @27
    @37
    cA
    @11
    cle
    wbr
    #
    @11
    cB
    cle
    wbr
    #
    @3
    @26
    @37
    @39
    @40
    w3a
    #
    @0
    @1
    @26
    @41
    wb
    @2
    cA
    cB
    @11
    elicc2
    3adant3
    biimpa
    simp1d
    #
    @38
    cA
    cB
    @34
    @13
    cA
    @11
    @34
    eqid
    @13
    eqid
    iccshftl
    syl22anc
    mpbid
    @27
    @12
    @13
    @27
    @12
    @27
    @11
    cA
    @42
    @38
    resubcld
    #
    recnd
    #
    @27
    @13
    @3
    @13
    crp
    wcel
    #
    @26
    @0
    @1
    @2
    @45
    cA
    cB
    difrp
    biimp3a
    adantr
    #
    rpcnd
    #
    @27
    @13
    @46
    rpne0d
    #
    divcan1d
    @27
    @30
    @34
    @31
    @13
    cicc
    @27
    @30
    cc0
    @34
    @27
    @13
    @47
    mul02d
    @27
    cA
    @27
    cA
    @38
    recnd
    #
    subidd
    eqtr4d
    @27
    @13
    @47
    mulid2d
    oveq12d
    3eltr4d
    @27
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @14
    cr
    wcel
    @45
    @28
    @33
    wb
    @27
    0red
    @27
    1red
    @27
    @12
    @13
    @43
    @46
    rerpdivcld
    @46
    cc0
    c1
    @30
    @31
    @13
    @14
    @30
    eqid
    @31
    eqid
    iccdil
    syl22anc
    mpbird
    @3
    @15
    @26
    wa
    wa
    #
    @6
    @14
    wceq
    #
    @12
    @6
    @13
    cmul
    co
    #
    wceq
    #
    @11
    @52
    cA
    caddc
    co
    #
    wceq
    #
    @11
    @10
    wceq
    @51
    @14
    @6
    wceq
    @50
    @53
    @6
    @14
    eqcom
    @50
    @12
    @6
    @13
    @3
    @26
    @12
    cc
    wcel
    @15
    @44
    adantrl
    @3
    @15
    @23
    @26
    @19
    adantrr
    @3
    @26
    @13
    cc
    wcel
    @15
    @47
    adantrl
    @3
    @26
    @13
    cc0
    wne
    @15
    @48
    adantrl
    divmul3d
    syl5bb
    @50
    @53
    @54
    @11
    wceq
    @55
    @50
    @11
    cA
    @52
    @50
    @11
    @3
    @26
    @37
    @15
    @42
    adantrl
    recnd
    @3
    @26
    cA
    cc
    wcel
    @15
    @49
    adantrl
    @50
    @52
    @3
    @15
    @52
    cr
    wcel
    @26
    @16
    @6
    @13
    @18
    @16
    cB
    cA
    @20
    @24
    resubcld
    remulcld
    adantrr
    recnd
    subadd2d
    @54
    @11
    eqcom
    syl6bb
    @50
    @54
    @10
    @11
    @3
    @15
    @54
    @10
    wceq
    @26
    @16
    @7
    @6
    cA
    cmul
    co
    #
    cmin
    co
    #
    cA
    caddc
    co
    @7
    cA
    @56
    cmin
    co
    #
    caddc
    co
    @54
    @10
    @16
    @7
    @56
    cA
    @22
    @16
    @6
    cA
    @19
    @25
    mulcld
    @25
    subadd23d
    @16
    @52
    @57
    cA
    caddc
    @16
    @6
    cB
    cA
    @19
    @21
    @25
    subdid
    oveq1d
    @16
    @9
    @58
    @7
    caddc
    @16
    @9
    c1
    cA
    cmul
    co
    #
    @56
    cmin
    co
    @58
    @16
    c1
    @6
    cA
    @16
    1cnd
    @19
    @25
    subdird
    @16
    @59
    cA
    @56
    cmin
    @16
    cA
    @25
    mulid2d
    oveq1d
    eqtrd
    oveq2d
    3eqtr4d
    adantrr
    eqeq2d
    3bitrd
    f1ocnv2d
end
