include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "1re.mm"
include "rpred.mm"
include "resubcl.mm"
include "sylancr.mm"
include "recxpcld.mm"
include "adantr.mm"
include "1red.mm"
include "w3a.mm"
include "recxpcl.mm"
include "cxpge0.mm"
include "jca.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "0le1.mm"
include "a1i.mm"
include "crp.mm"
include "wb.mm"
include "difrp.mm"
include "sylancl.mm"
include "biimpa.mm"
include "cxple2d.mm"
include "mpbid.mm"
include "recnd.mm"
include "1cxpd.mm"
include "breqtrd.mm"
include "simpr.mm"
include "oveq2d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "cc.mm"
include "cxp0d.mm"
include "eqtrd.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "wo.mm"
include "leloe.mm"
include "mpjaodan.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "caddc.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "anim1i.mm"
include "elrp.mm"
include "sylibr.mm"
include "rpne0d.mm"
include "cxpaddd.mm"
include "cxp1d.mm"
include "3eqtr3d.mm"
include "cxpcld.mm"
include "mulid2d.mm"
include "3brtr3d.mm"
include "cxpge0d.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "0re.mm"

theorem cxpaddlelem
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cxpaddlelem.1: |- ( ph -> A e. RR )
  assume cxpaddlelem.2: |- ( ph -> 0 <_ A )
  assume cxpaddlelem.3: |- ( ph -> A <_ 1 )
  assume cxpaddlelem.4: |- ( ph -> B e. RR+ )
  assume cxpaddlelem.5: |- ( ph -> B <_ 1 )


  assert |- ( ph -> A <_ ( A ^c B ) )

  proof
    wph
    cc0
    cA
    clt
    wbr
    #
    cA
    cA
    cB
    ccxp
    co
    #
    cle
    wbr
    #
    cc0
    cA
    wceq
    #
    wph
    @0
    wa
    #
    cA
    c1
    cB
    cmin
    co
    #
    ccxp
    co
    #
    @1
    cmul
    co
    #
    c1
    @1
    cmul
    co
    #
    cA
    @1
    cle
    @4
    @6
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    @6
    c1
    cle
    wbr
    #
    @7
    @8
    cle
    wbr
    wph
    @9
    @0
    wph
    cA
    @5
    cxpaddlelem.1
    cxpaddlelem.2
    wph
    @10
    cB
    cr
    wcel
    #
    @5
    cr
    wcel
    1re
    wph
    cB
    cxpaddlelem.4
    rpred
    #
    c1
    cB
    resubcl
    sylancr
    #
    recxpcld
    adantr
    @4
    1red
    wph
    @13
    @0
    wph
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    @15
    @13
    cxpaddlelem.1
    cxpaddlelem.2
    @16
    @18
    @19
    @15
    w3a
    @11
    @12
    cA
    cB
    recxpcl
    cA
    cB
    cxpge0
    jca
    syl3anc
    adantr
    @4
    cB
    c1
    clt
    wbr
    #
    @14
    cB
    c1
    wceq
    #
    @4
    @20
    wa
    #
    @6
    c1
    @5
    ccxp
    co
    #
    c1
    cle
    @22
    cA
    c1
    cle
    wbr
    #
    @6
    @23
    cle
    wbr
    wph
    @24
    @0
    @20
    cxpaddlelem.3
    ad2antrr
    @22
    cA
    c1
    @5
    wph
    @18
    @0
    @20
    cxpaddlelem.1
    ad2antrr
    wph
    @19
    @0
    @20
    cxpaddlelem.2
    ad2antrr
    @22
    1red
    cc0
    c1
    cle
    wbr
    @22
    0le1
    a1i
    @4
    @20
    @5
    crp
    wcel
    #
    wph
    @20
    @25
    wb
    #
    @0
    wph
    @15
    @10
    @26
    @16
    1re
    cB
    c1
    difrp
    sylancl
    adantr
    biimpa
    cxple2d
    mpbid
    wph
    @23
    c1
    wceq
    @0
    @20
    wph
    @5
    wph
    @5
    @17
    recnd
    #
    1cxpd
    ad2antrr
    breqtrd
    @4
    @21
    wa
    #
    @6
    c1
    c1
    cle
    @28
    @6
    cA
    cc0
    ccxp
    co
    c1
    @28
    @5
    cc0
    cA
    ccxp
    @28
    @5
    c1
    c1
    cmin
    co
    cc0
    @28
    cB
    c1
    c1
    cmin
    @4
    @21
    simpr
    oveq2d
    1m1e0
    syl6eq
    oveq2d
    @28
    cA
    wph
    cA
    cc
    wcel
    #
    @0
    @21
    wph
    cA
    cxpaddlelem.1
    recnd
    #
    ad2antrr
    cxp0d
    eqtrd
    1le1
    syl6eqbr
    wph
    @20
    @21
    wo
    #
    @0
    wph
    cB
    c1
    cle
    wbr
    #
    @31
    cxpaddlelem.5
    wph
    @15
    @10
    @32
    @31
    wb
    @16
    1re
    cB
    c1
    leloe
    sylancl
    mpbid
    adantr
    mpjaodan
    @6
    c1
    @1
    lemul1a
    syl31anc
    @4
    cA
    @5
    cB
    caddc
    co
    #
    ccxp
    co
    cA
    c1
    ccxp
    co
    #
    @7
    cA
    @4
    @33
    c1
    cA
    ccxp
    wph
    @33
    c1
    wceq
    #
    @0
    wph
    c1
    cc
    wcel
    cB
    cc
    wcel
    #
    @35
    ax-1cn
    wph
    cB
    @16
    recnd
    #
    c1
    cB
    npcan
    sylancr
    adantr
    oveq2d
    @4
    cA
    @5
    cB
    wph
    @29
    @0
    @30
    adantr
    @4
    cA
    @4
    @18
    @0
    wa
    cA
    crp
    wcel
    wph
    @18
    @0
    cxpaddlelem.1
    anim1i
    cA
    elrp
    sylibr
    rpne0d
    wph
    @5
    cc
    wcel
    @0
    @27
    adantr
    wph
    @36
    @0
    @37
    adantr
    cxpaddd
    wph
    @34
    cA
    wceq
    @0
    wph
    cA
    @30
    cxp1d
    adantr
    3eqtr3d
    wph
    @8
    @1
    wceq
    @0
    wph
    @1
    wph
    cA
    cB
    @30
    @37
    cxpcld
    mulid2d
    adantr
    3brtr3d
    wph
    @3
    @2
    wph
    @12
    @3
    @2
    wph
    cA
    cB
    cxpaddlelem.1
    cxpaddlelem.2
    @16
    cxpge0d
    cc0
    cA
    @1
    cle
    breq1
    syl5ibcom
    imp
    wph
    @19
    @0
    @3
    wo
    #
    cxpaddlelem.2
    wph
    cc0
    cr
    wcel
    @18
    @19
    @38
    wb
    0re
    cxpaddlelem.1
    cc0
    cA
    leloe
    sylancr
    mpbid
    mpjaodan
end
