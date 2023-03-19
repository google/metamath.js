include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ccxp.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "readdcld.mm"
include "addge0d.mm"
include "rpred.mm"
include "recxpcld.mm"
include "adantr.mm"
include "recnd.mm"
include "mulid2d.mm"
include "cdiv.mm"
include "crp.mm"
include "anim1i.mm"
include "elrp.mm"
include "sylibr.mm"
include "rerpdivcld.mm"
include "simpr.mm"
include "divge0.mm"
include "syl22anc.mm"
include "addge01d.mm"
include "mpbid.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "1red.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "cxpaddlelem.mm"
include "addge02d.mm"
include "le2addd.mm"
include "rpne0d.mm"
include "divdird.mm"
include "dividd.mm"
include "eqtr3d.mm"
include "cc.mm"
include "divcxpd.mm"
include "oveq12d.mm"
include "rpcxpcld.mm"
include "eqtr4d.mm"
include "3brtr3d.mm"
include "lemuldivd.mm"
include "eqbrtrrd.mm"
include "0cxpd.mm"
include "cxpge0d.mm"
include "eqbrtrd.mm"
include "oveq1.mm"
include "breq1d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "wo.mm"
include "0re.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpjaodan.mm"

theorem cxpaddle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume cxpaddle.1: |- ( ph -> A e. RR )
  assume cxpaddle.2: |- ( ph -> 0 <_ A )
  assume cxpaddle.3: |- ( ph -> B e. RR )
  assume cxpaddle.4: |- ( ph -> 0 <_ B )
  assume cxpaddle.5: |- ( ph -> C e. RR+ )
  assume cxpaddle.6: |- ( ph -> C <_ 1 )


  assert |- ( ph -> ( ( A + B ) ^c C ) <_ ( ( A ^c C ) + ( B ^c C ) ) )

  proof
    wph
    cc0
    cA
    cB
    caddc
    co
    #
    clt
    wbr
    #
    @0
    cC
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    cB
    cC
    ccxp
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    cc0
    @0
    wceq
    #
    wph
    @1
    wa
    #
    c1
    @2
    cmul
    co
    #
    @2
    @5
    cle
    @8
    @2
    @8
    @2
    wph
    @2
    cr
    wcel
    @1
    wph
    @0
    cC
    wph
    cA
    cB
    cxpaddle.1
    cxpaddle.3
    readdcld
    #
    wph
    cA
    cB
    cxpaddle.1
    cxpaddle.3
    cxpaddle.2
    cxpaddle.4
    addge0d
    #
    wph
    cC
    cxpaddle.5
    rpred
    #
    recxpcld
    adantr
    recnd
    #
    mulid2d
    @8
    @9
    @5
    cle
    wbr
    c1
    @5
    @2
    cdiv
    co
    #
    cle
    wbr
    @8
    cA
    @0
    cdiv
    co
    #
    cB
    @0
    cdiv
    co
    #
    caddc
    co
    #
    @15
    cC
    ccxp
    co
    #
    @16
    cC
    ccxp
    co
    #
    caddc
    co
    #
    c1
    @14
    cle
    @8
    @15
    @16
    @18
    @19
    @8
    cA
    @0
    wph
    cA
    cr
    wcel
    #
    @1
    cxpaddle.1
    adantr
    #
    @8
    @0
    cr
    wcel
    #
    @1
    wa
    @0
    crp
    wcel
    wph
    @23
    @1
    @10
    anim1i
    @0
    elrp
    sylibr
    #
    rerpdivcld
    #
    @8
    cB
    @0
    wph
    cB
    cr
    wcel
    #
    @1
    cxpaddle.3
    adantr
    #
    @24
    rerpdivcld
    #
    @8
    @15
    cC
    @25
    @8
    @21
    cc0
    cA
    cle
    wbr
    #
    @23
    @1
    cc0
    @15
    cle
    wbr
    @22
    wph
    @29
    @1
    cxpaddle.2
    adantr
    #
    wph
    @23
    @1
    @10
    adantr
    #
    wph
    @1
    simpr
    #
    cA
    @0
    divge0
    syl22anc
    #
    wph
    cC
    cr
    wcel
    @1
    @12
    adantr
    #
    recxpcld
    @8
    @16
    cC
    @28
    @8
    @26
    cc0
    cB
    cle
    wbr
    #
    @23
    @1
    cc0
    @16
    cle
    wbr
    @27
    wph
    @35
    @1
    cxpaddle.4
    adantr
    #
    @31
    @32
    cB
    @0
    divge0
    syl22anc
    #
    @34
    recxpcld
    @8
    @15
    cC
    @25
    @33
    @8
    @15
    c1
    cle
    wbr
    #
    cA
    @0
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @8
    cA
    @0
    @39
    cle
    wph
    cA
    @0
    cle
    wbr
    #
    @1
    wph
    @35
    @41
    cxpaddle.4
    wph
    cA
    cB
    cxpaddle.1
    cxpaddle.3
    addge01d
    mpbid
    adantr
    @8
    @0
    @8
    @0
    @31
    recnd
    #
    mulid1d
    #
    breqtrrd
    @8
    @21
    c1
    cr
    wcel
    #
    @23
    @1
    @38
    @40
    wb
    @22
    @8
    1red
    #
    @31
    @32
    cA
    c1
    @0
    ledivmul
    syl112anc
    mpbird
    wph
    cC
    crp
    wcel
    @1
    cxpaddle.5
    adantr
    #
    wph
    cC
    c1
    cle
    wbr
    @1
    cxpaddle.6
    adantr
    #
    cxpaddlelem
    @8
    @16
    cC
    @28
    @37
    @8
    @16
    c1
    cle
    wbr
    #
    cB
    @39
    cle
    wbr
    #
    @8
    cB
    @0
    @39
    cle
    wph
    cB
    @0
    cle
    wbr
    #
    @1
    wph
    @29
    @50
    cxpaddle.2
    wph
    cB
    cA
    cxpaddle.3
    cxpaddle.1
    addge02d
    mpbid
    adantr
    @43
    breqtrrd
    @8
    @26
    @44
    @23
    @1
    @48
    @49
    wb
    @27
    @45
    @31
    @32
    cB
    c1
    @0
    ledivmul
    syl112anc
    mpbird
    @46
    @47
    cxpaddlelem
    le2addd
    @8
    @0
    @0
    cdiv
    co
    @17
    c1
    @8
    cA
    cB
    @0
    @8
    cA
    @22
    recnd
    @8
    cB
    @27
    recnd
    @42
    @8
    @0
    @24
    rpne0d
    #
    divdird
    @8
    @0
    @42
    @51
    dividd
    eqtr3d
    @8
    @20
    @3
    @2
    cdiv
    co
    #
    @4
    @2
    cdiv
    co
    #
    caddc
    co
    @14
    @8
    @18
    @52
    @19
    @53
    caddc
    @8
    cA
    @0
    cC
    @22
    @30
    @24
    wph
    cC
    cc
    wcel
    @1
    wph
    cC
    @12
    recnd
    #
    adantr
    #
    divcxpd
    @8
    cB
    @0
    cC
    @27
    @36
    @24
    @55
    divcxpd
    oveq12d
    @8
    @3
    @4
    @2
    wph
    @3
    cc
    wcel
    @1
    wph
    @3
    wph
    cA
    cC
    cxpaddle.1
    cxpaddle.2
    @12
    recxpcld
    #
    recnd
    adantr
    wph
    @4
    cc
    wcel
    @1
    wph
    @4
    wph
    cB
    cC
    cxpaddle.3
    cxpaddle.4
    @12
    recxpcld
    #
    recnd
    adantr
    @13
    @8
    @2
    @8
    @0
    cC
    @24
    @34
    rpcxpcld
    #
    rpne0d
    divdird
    eqtr4d
    3brtr3d
    @8
    c1
    @5
    @2
    @45
    wph
    @5
    cr
    wcel
    @1
    wph
    @3
    @4
    @56
    @57
    readdcld
    adantr
    @58
    lemuldivd
    mpbird
    eqbrtrrd
    wph
    @7
    @6
    wph
    cc0
    cC
    ccxp
    co
    #
    @5
    cle
    wbr
    @7
    @6
    wph
    @59
    cc0
    @5
    cle
    wph
    cC
    @54
    wph
    cC
    cxpaddle.5
    rpne0d
    0cxpd
    wph
    @3
    @4
    @56
    @57
    wph
    cA
    cC
    cxpaddle.1
    cxpaddle.2
    @12
    cxpge0d
    wph
    cB
    cC
    cxpaddle.3
    cxpaddle.4
    @12
    cxpge0d
    addge0d
    eqbrtrd
    @7
    @59
    @2
    @5
    cle
    cc0
    @0
    cC
    ccxp
    oveq1
    breq1d
    syl5ibcom
    imp
    wph
    cc0
    @0
    cle
    wbr
    #
    @1
    @7
    wo
    #
    @11
    wph
    cc0
    cr
    wcel
    @23
    @60
    @61
    wb
    0re
    @10
    cc0
    @0
    leloe
    sylancr
    mpbid
    mpjaodan
end
