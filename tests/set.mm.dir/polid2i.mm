include "c4.mm"
include "csp.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "cmin.mm"
include "ci.mm"
include "csm.mm"
include "cmul.mm"
include "caddc.mm"
include "4cn.mm"
include "hicli.mm"
include "4ne0.mm"
include "c2.mm"
include "2cn.mm"
include "addcli.mm"
include "subcli.mm"
include "adddii.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ppncan.mm"
include "mp3an.mm"
include "2timesi.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "mulassi.mm"
include "2t2e4.mm"
include "oveq1i.mm"
include "3eqtr2ri.mm"
include "pnncani.mm"
include "normlem8.mm"
include "normlem9.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"
include "cneg.mm"
include "ax-icn.mm"
include "hvmulcli.mm"
include "ccj.mm"
include "cfv.mm"
include "chil.mm"
include "his5.mm"
include "cji.mm"
include "eqtri.mm"
include "ax-his3.mm"
include "eqtr3i.mm"
include "3eqtri.mm"
include "negicn.mm"
include "mulcli.mm"
include "mul12i.mm"
include "c1.mm"
include "mulneg2i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "mulid2i.mm"
include "3eqtr3i.mm"
include "mulm1i.mm"
include "negsubi.mm"
include "3eqtr2i.mm"
include "mvllmuli.mm"

theorem polid2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume polid2.1: |- A e. ~H
  assume polid2.2: |- B e. ~H
  assume polid2.3: |- C e. ~H
  assume polid2.4: |- D e. ~H


  assert |- ( A .ih B ) = ( ( ( ( ( A +h C ) .ih ( D +h B ) ) - ( ( A -h C ) .ih ( D -h B ) ) ) + ( _i x. ( ( ( A +h ( _i .h C ) ) .ih ( D +h ( _i .h B ) ) ) - ( ( A -h ( _i .h C ) ) .ih ( D -h ( _i .h B ) ) ) ) ) ) / 4 )

  proof
    c4
    cA
    cB
    csp
    co
    #
    cA
    cC
    cva
    co
    cD
    cB
    cva
    co
    csp
    co
    #
    cA
    cC
    cmv
    co
    cD
    cB
    cmv
    co
    csp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cC
    csm
    co
    #
    cva
    co
    cD
    ci
    cB
    csm
    co
    #
    cva
    co
    csp
    co
    #
    cA
    @4
    cmv
    co
    cD
    @5
    cmv
    co
    csp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    4cn
    cA
    cB
    polid2.1
    polid2.2
    hicli
    #
    4ne0
    c2
    @0
    cC
    cD
    csp
    co
    #
    caddc
    co
    #
    @0
    @12
    cmin
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    c2
    @13
    cmul
    co
    #
    c2
    @14
    cmul
    co
    #
    caddc
    co
    c4
    @0
    cmul
    co
    #
    @10
    c2
    @13
    @14
    2cn
    @0
    @12
    @11
    cC
    cD
    polid2.3
    polid2.4
    hicli
    #
    addcli
    #
    @0
    @12
    @11
    @20
    subcli
    adddii
    @16
    c2
    c2
    @0
    cmul
    co
    #
    cmul
    co
    c2
    c2
    cmul
    co
    #
    @0
    cmul
    co
    @19
    @15
    @22
    c2
    cmul
    @15
    @0
    @0
    caddc
    co
    #
    @22
    @0
    cc
    wcel
    #
    @12
    cc
    wcel
    @25
    @15
    @24
    wceq
    @11
    @20
    @11
    @0
    @12
    @0
    ppncan
    mp3an
    @0
    @11
    2timesi
    eqtr4i
    oveq2i
    c2
    c2
    @0
    2cn
    2cn
    @11
    mulassi
    @23
    c4
    @0
    cmul
    2t2e4
    oveq1i
    3eqtr2ri
    @3
    @17
    @9
    @18
    caddc
    cA
    cD
    csp
    co
    #
    cC
    cB
    csp
    co
    #
    caddc
    co
    #
    @13
    caddc
    co
    #
    @28
    @13
    cmin
    co
    #
    cmin
    co
    @13
    @13
    caddc
    co
    @3
    @17
    @28
    @13
    @13
    @26
    @27
    cA
    cD
    polid2.1
    polid2.4
    hicli
    #
    cC
    cB
    polid2.3
    polid2.2
    hicli
    addcli
    @21
    @21
    pnncani
    @1
    @29
    @2
    @30
    cmin
    cA
    cC
    cD
    cB
    polid2.1
    polid2.3
    polid2.4
    polid2.2
    normlem8
    cA
    cC
    cD
    cB
    polid2.1
    polid2.3
    polid2.4
    polid2.2
    normlem9
    oveq12i
    @13
    @21
    2timesi
    3eqtr4i
    @9
    ci
    c2
    ci
    cneg
    #
    @0
    cmul
    co
    #
    ci
    @12
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cmul
    co
    c2
    ci
    @35
    cmul
    co
    #
    cmul
    co
    @18
    @8
    @36
    ci
    cmul
    @8
    @26
    @4
    @5
    csp
    co
    #
    caddc
    co
    #
    cA
    @5
    csp
    co
    #
    @4
    cD
    csp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @39
    @42
    cmin
    co
    #
    cmin
    co
    @42
    @42
    caddc
    co
    #
    @36
    @6
    @43
    @7
    @44
    cmin
    cA
    @4
    cD
    @5
    polid2.1
    ci
    cC
    ax-icn
    polid2.3
    hvmulcli
    #
    polid2.4
    ci
    cB
    ax-icn
    polid2.2
    hvmulcli
    #
    normlem8
    cA
    @4
    cD
    @5
    polid2.1
    @46
    polid2.4
    @47
    normlem9
    oveq12i
    @39
    @42
    @42
    @26
    @38
    @31
    @4
    @5
    @46
    @47
    hicli
    addcli
    @40
    @41
    cA
    @5
    polid2.1
    @47
    hicli
    @4
    cD
    @46
    polid2.4
    hicli
    addcli
    #
    @48
    pnncani
    c2
    @42
    cmul
    co
    @45
    @36
    @42
    @48
    2timesi
    @42
    @35
    c2
    cmul
    @40
    @33
    @41
    @34
    caddc
    @40
    ci
    ccj
    cfv
    #
    @0
    cmul
    co
    #
    @33
    ci
    cc
    wcel
    #
    cA
    chil
    wcel
    cB
    chil
    wcel
    @40
    @50
    wceq
    ax-icn
    polid2.1
    polid2.2
    ci
    cA
    cB
    his5
    mp3an
    @49
    @32
    @0
    cmul
    cji
    oveq1i
    eqtri
    @51
    cC
    chil
    wcel
    cD
    chil
    wcel
    @41
    @34
    wceq
    ax-icn
    polid2.3
    polid2.4
    ci
    cC
    cD
    ax-his3
    mp3an
    oveq12i
    oveq2i
    eqtr3i
    3eqtri
    oveq2i
    c2
    ci
    @35
    2cn
    ax-icn
    @33
    @34
    @32
    @0
    negicn
    @11
    mulcli
    #
    ci
    @12
    ax-icn
    @20
    mulcli
    #
    addcli
    mul12i
    @37
    @14
    c2
    cmul
    @37
    ci
    @33
    cmul
    co
    #
    ci
    @34
    cmul
    co
    #
    caddc
    co
    @0
    @12
    cneg
    #
    caddc
    co
    @14
    ci
    @33
    @34
    ax-icn
    @52
    @53
    adddii
    @54
    @0
    @55
    @56
    caddc
    ci
    @32
    cmul
    co
    #
    @0
    cmul
    co
    c1
    @0
    cmul
    co
    @54
    @0
    @57
    c1
    @0
    cmul
    @57
    ci
    ci
    cmul
    co
    #
    cneg
    c1
    cneg
    #
    cneg
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg2i
    @58
    @59
    ixi
    negeqi
    negneg1e1
    3eqtri
    oveq1i
    ci
    @32
    @0
    ax-icn
    negicn
    @11
    mulassi
    @0
    @11
    mulid2i
    3eqtr3i
    @58
    @12
    cmul
    co
    @59
    @12
    cmul
    co
    @55
    @56
    @58
    @59
    @12
    cmul
    ixi
    oveq1i
    ci
    ci
    @12
    ax-icn
    ax-icn
    @20
    mulassi
    @12
    @20
    mulm1i
    3eqtr3i
    oveq12i
    @0
    @12
    @11
    @20
    negsubi
    3eqtri
    oveq2i
    3eqtr2i
    oveq12i
    3eqtr4i
    mvllmuli
end
