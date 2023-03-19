include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "w3a.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wss.mm"
include "iccss2.mm"
include "adantl.mm"
include "3adantr3.mm"
include "adantr.mm"
include "iccssre.mm"
include "sselda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "jca.mm"
include "simpr3.mm"
include "wi.mm"
include "lincmb01cmp.mm"
include "ex.mm"
include "3expa.mm"
include "imp.mm"
include "an32s.mm"
include "sylan.mm"
include "sseldd.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cc.mm"
include "unitssre.mm"
include "sseli.mm"
include "recnd.mm"
include "ad2antll.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "mpan.mm"
include "subcl.mm"
include "ancri.mm"
include "adddir.mm"
include "mulid2.mm"
include "3eqtr3d.mm"
include "syl2anc.mm"
include "3adantr1.mm"
include "sylan9eqr.mm"
include "simplr2.mm"
include "eqeltrd.mm"
include "ancom2s.mm"
include "iirev.mm"
include "sseldi.mm"
include "recn.mm"
include "mulcl.mm"
include "syl2anr.mm"
include "adantll.mm"
include "adantlr.mm"
include "addcomd.mm"
include "3adantl3.mm"
include "nncan.mm"
include "eqcomd.mm"
include "syl.mm"
include "eqtrd.mm"
include "sylan2.mm"
include "w3o.mm"
include "lttri4d.mm"
include "mpjao3dan.mm"

theorem icccvx
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( C e. ( A [,] B ) /\ D e. ( A [,] B ) /\ T e. ( 0 [,] 1 ) ) -> ( ( ( 1 - T ) x. C ) + ( T x. D ) ) e. ( A [,] B ) ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cC
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cD
    @1
    wcel
    #
    cT
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    w3a
    #
    c1
    cT
    cmin
    co
    #
    cC
    cmul
    co
    #
    cT
    cD
    cmul
    co
    #
    caddc
    co
    #
    @1
    wcel
    #
    @0
    @6
    wa
    #
    cC
    cD
    clt
    wbr
    #
    @11
    cC
    cD
    wceq
    #
    cD
    cC
    clt
    wbr
    #
    @12
    @13
    wa
    cC
    cD
    cicc
    co
    #
    @1
    @10
    @12
    @16
    @1
    wss
    #
    @13
    @0
    @2
    @3
    @17
    @5
    @2
    @3
    wa
    #
    @17
    @0
    cA
    cB
    cC
    cD
    iccss2
    adantl
    3adantr3
    adantr
    @12
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    @5
    wa
    @13
    @10
    @16
    wcel
    #
    @12
    @21
    @5
    @0
    @2
    @3
    @21
    @5
    @0
    @18
    wa
    #
    @19
    @20
    @0
    @2
    @19
    @3
    @0
    @1
    cr
    cC
    cA
    cB
    iccssre
    #
    sselda
    adantrr
    #
    @0
    @3
    @20
    @2
    @0
    @1
    cr
    cD
    @24
    sselda
    #
    adantrl
    #
    jca
    3adantr3
    @0
    @2
    @3
    @5
    simpr3
    #
    jca
    @21
    @13
    @5
    @22
    @21
    @13
    wa
    @5
    @22
    @19
    @20
    @13
    @5
    @22
    wi
    @19
    @20
    @13
    w3a
    @5
    @22
    cC
    cD
    cT
    lincmb01cmp
    ex
    3expa
    imp
    an32s
    sylan
    sseldd
    @12
    @14
    wa
    @10
    cD
    @1
    @14
    @12
    @10
    @7
    cD
    cmul
    co
    #
    @9
    caddc
    co
    #
    cD
    @14
    @8
    @29
    @9
    caddc
    cC
    cD
    @7
    cmul
    oveq2
    oveq1d
    @0
    @3
    @5
    @30
    cD
    wceq
    #
    @2
    @0
    @3
    @5
    wa
    wa
    cT
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    @31
    @5
    @32
    @0
    @3
    @5
    cT
    @4
    cr
    cT
    unitssre
    sseli
    recnd
    #
    ad2antll
    @0
    @3
    @33
    @5
    @0
    @3
    wa
    cD
    @26
    recnd
    adantrr
    @32
    @33
    wa
    #
    @7
    cT
    caddc
    co
    #
    cD
    cmul
    co
    #
    c1
    cD
    cmul
    co
    #
    @30
    cD
    @35
    @36
    c1
    cD
    cmul
    @32
    @36
    c1
    wceq
    #
    @33
    c1
    cc
    wcel
    #
    @32
    @39
    ax-1cn
    c1
    cT
    npcan
    mpan
    adantr
    oveq1d
    @32
    @7
    cc
    wcel
    #
    @32
    wa
    @33
    @37
    @30
    wceq
    #
    @32
    @41
    @40
    @32
    @41
    ax-1cn
    c1
    cT
    subcl
    mpan
    ancri
    @41
    @32
    @33
    @42
    @7
    cT
    cD
    adddir
    3expa
    sylan
    @33
    @38
    cD
    wceq
    @32
    cD
    mulid2
    adantl
    3eqtr3d
    syl2anc
    3adantr1
    sylan9eqr
    @2
    @3
    @5
    @0
    @14
    simplr2
    eqeltrd
    @12
    @15
    wa
    cD
    cC
    cicc
    co
    #
    @1
    @10
    @12
    @43
    @1
    wss
    #
    @15
    @0
    @2
    @3
    @44
    @5
    @0
    @3
    @2
    @44
    @3
    @2
    wa
    @44
    @0
    cA
    cB
    cD
    cC
    iccss2
    adantl
    ancom2s
    3adantr3
    adantr
    @12
    @20
    @19
    wa
    #
    @5
    wa
    #
    @15
    @10
    @43
    wcel
    #
    @12
    @45
    @5
    @0
    @2
    @3
    @45
    @5
    @23
    @20
    @19
    @27
    @25
    jca
    3adantr3
    @28
    jca
    @45
    @15
    @5
    @47
    @45
    @15
    wa
    @5
    @47
    @20
    @19
    @15
    @5
    @47
    wi
    @20
    @19
    @15
    w3a
    #
    @5
    @47
    @48
    @5
    wa
    #
    @10
    c1
    @7
    cmin
    co
    #
    cD
    cmul
    co
    #
    @8
    caddc
    co
    #
    @43
    @49
    @10
    @9
    @8
    caddc
    co
    #
    @52
    @20
    @19
    @5
    @10
    @53
    wceq
    @15
    @46
    @8
    @9
    @19
    @5
    @8
    cc
    wcel
    #
    @20
    @5
    @41
    cC
    cc
    wcel
    @54
    @19
    @5
    @7
    @5
    @4
    cr
    @7
    unitssre
    cT
    iirev
    #
    sseldi
    recnd
    cC
    recn
    @7
    cC
    mulcl
    syl2anr
    adantll
    @20
    @5
    @9
    cc
    wcel
    #
    @19
    @5
    @32
    @33
    @56
    @20
    @34
    cD
    recn
    cT
    cD
    mulcl
    syl2anr
    adantlr
    addcomd
    3adantl3
    @5
    @53
    @52
    wceq
    #
    @48
    @5
    @32
    @57
    @34
    @32
    @9
    @51
    @8
    caddc
    @32
    cT
    @50
    cD
    cmul
    @32
    @50
    cT
    @40
    @32
    @50
    cT
    wceq
    ax-1cn
    c1
    cT
    nncan
    mpan
    eqcomd
    oveq1d
    oveq1d
    syl
    adantl
    eqtrd
    @5
    @48
    @7
    @4
    wcel
    @52
    @43
    wcel
    @55
    cD
    cC
    @7
    lincmb01cmp
    sylan2
    eqeltrd
    ex
    3expa
    imp
    an32s
    sylan
    sseldd
    @0
    @2
    @3
    @13
    @14
    @15
    w3o
    @5
    @23
    cC
    cD
    @25
    @27
    lttri4d
    3adantr3
    mpjao3dan
    ex
end
