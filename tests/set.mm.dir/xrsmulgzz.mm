include "cxr.mm"
include "wcel.mm"
include "cz.mm"
include "cxrs.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cxmu.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "xrsbas.mm"
include "xrs0.mm"
include "eqid.mm"
include "mulg0.mm"
include "xmul02.mm"
include "eqtr4d.mm"
include "cn0.mm"
include "wa.mm"
include "cxad.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cn.mm"
include "simpll.mm"
include "xrsadd.mm"
include "mulgnnp1.mm"
include "syl2anc.mm"
include "xaddid2.mm"
include "adantl.mm"
include "simpl.mm"
include "eqtrd.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "mulg1.mm"
include "3eqtr4rd.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "sseldi.mm"
include "nn0ge0.mm"
include "ad2antlr.mm"
include "1re.mm"
include "rexri.mm"
include "a1i.mm"
include "0le1.mm"
include "xadddi2r.mm"
include "syl221anc.mm"
include "rexadd.mm"
include "xmulid2.mm"
include "syl.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "3eqtr4d.mm"
include "exp31.mm"
include "cxne.mm"
include "xnegeq.mm"
include "cminusg.mm"
include "mulgnegnn.mm"
include "ancoms.mm"
include "cvv.mm"
include "xrsex.mm"
include "wss.mm"
include "ssid.mm"
include "w3a.mm"
include "simp2.mm"
include "simp3.mm"
include "xaddcld.mm"
include "mulgnnsubcl.mm"
include "3anidm12.mm"
include "xrsinvgval.mm"
include "nnre.mm"
include "rexneg.mm"
include "nnssre.mm"
include "xmulneg1.mm"
include "eqtr3d.mm"
include "zindd.mm"
include "impcom.mm"

theorem xrsmulgzz
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ZZ /\ B e. RR* ) -> ( A ( .g ` RR*s ) B ) = ( A *e B ) )

  proof
    cB
    cxr
    wcel
    #
    cA
    cz
    wcel
    cA
    cB
    cxrs
    cmg
    cfv
    #
    co
    #
    cA
    cB
    cxmu
    co
    #
    wceq
    #
    vn
    cv
    #
    cB
    @1
    co
    #
    @5
    cB
    cxmu
    co
    #
    wceq
    cc0
    cB
    @1
    co
    #
    cc0
    cB
    cxmu
    co
    #
    wceq
    vm
    cv
    #
    cB
    @1
    co
    #
    @10
    cB
    cxmu
    co
    #
    wceq
    #
    @10
    cneg
    #
    cB
    @1
    co
    #
    @14
    cB
    cxmu
    co
    #
    wceq
    #
    @10
    c1
    caddc
    co
    #
    cB
    @1
    co
    #
    @18
    cB
    cxmu
    co
    #
    wceq
    #
    @4
    @0
    vn
    vm
    cA
    @5
    cc0
    wceq
    @6
    @8
    @7
    @9
    @5
    cc0
    cB
    @1
    oveq1
    @5
    cc0
    cB
    cxmu
    oveq1
    eqeq12d
    @5
    @10
    wceq
    @6
    @11
    @7
    @12
    @5
    @10
    cB
    @1
    oveq1
    @5
    @10
    cB
    cxmu
    oveq1
    eqeq12d
    @5
    @18
    wceq
    @6
    @19
    @7
    @20
    @5
    @18
    cB
    @1
    oveq1
    @5
    @18
    cB
    cxmu
    oveq1
    eqeq12d
    @5
    @14
    wceq
    @6
    @15
    @7
    @16
    @5
    @14
    cB
    @1
    oveq1
    @5
    @14
    cB
    cxmu
    oveq1
    eqeq12d
    @5
    cA
    wceq
    @6
    @2
    @7
    @3
    @5
    cA
    cB
    @1
    oveq1
    @5
    cA
    cB
    cxmu
    oveq1
    eqeq12d
    @0
    @8
    cc0
    @9
    cxr
    @1
    cxrs
    cB
    cc0
    xrsbas
    xrs0
    @1
    eqid
    #
    mulg0
    #
    cB
    xmul02
    eqtr4d
    @0
    @10
    cn0
    wcel
    #
    @13
    @21
    @0
    @24
    wa
    #
    @13
    wa
    #
    @11
    cB
    cxad
    co
    #
    @12
    cB
    cxad
    co
    #
    @19
    @20
    @26
    @11
    @12
    cB
    cxad
    @25
    @13
    simpr
    oveq1d
    @25
    @19
    @27
    wceq
    #
    @13
    @25
    @10
    cn
    wcel
    #
    @29
    @10
    cc0
    wceq
    #
    @25
    @30
    wa
    @30
    @0
    @29
    @25
    @30
    simpr
    @0
    @24
    @30
    simpll
    cxr
    cxad
    @1
    cxrs
    @10
    cB
    xrsbas
    @22
    xrsadd
    mulgnnp1
    syl2anc
    @25
    @31
    wa
    @31
    @0
    @29
    @25
    @31
    simpr
    @0
    @24
    @31
    simpll
    @31
    @0
    wa
    #
    cc0
    cB
    cxad
    co
    #
    cB
    @27
    @19
    @0
    @33
    cB
    wceq
    @31
    cB
    xaddid2
    adantl
    @32
    @11
    cc0
    cB
    cxad
    @32
    @11
    @8
    cc0
    @32
    @10
    cc0
    cB
    @1
    @31
    @0
    simpl
    #
    oveq1d
    @0
    @8
    cc0
    wceq
    @31
    @23
    adantl
    eqtrd
    oveq1d
    @32
    @19
    c1
    cB
    @1
    co
    #
    cB
    @32
    @18
    c1
    cB
    @1
    @32
    @18
    cc0
    c1
    caddc
    co
    c1
    @32
    @10
    cc0
    c1
    caddc
    @34
    oveq1d
    0p1e1
    syl6eq
    oveq1d
    @0
    @35
    cB
    wceq
    @31
    cxr
    @1
    cxrs
    cB
    xrsbas
    @22
    mulg1
    adantl
    eqtrd
    3eqtr4rd
    syl2anc
    @25
    @24
    @30
    @31
    wo
    @0
    @24
    simpr
    #
    @10
    elnn0
    sylib
    mpjaodan
    adantr
    @26
    @10
    c1
    cxad
    co
    #
    cB
    cxmu
    co
    #
    @12
    c1
    cB
    cxmu
    co
    #
    cxad
    co
    #
    @20
    @28
    @26
    @10
    cxr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    c1
    cxr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    @0
    @38
    @40
    wceq
    @26
    cn0
    cxr
    @10
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    @25
    @24
    @13
    @36
    adantr
    #
    sseldi
    @24
    @42
    @0
    @13
    @10
    nn0ge0
    ad2antlr
    @43
    @26
    c1
    1re
    rexri
    a1i
    @44
    @26
    0le1
    a1i
    @0
    @24
    @13
    simpll
    #
    @10
    c1
    cB
    xadddi2r
    syl221anc
    @26
    @37
    @18
    cB
    cxmu
    @26
    @10
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @37
    @18
    wceq
    @26
    cn0
    cr
    @10
    nn0ssre
    @45
    sseldi
    @48
    @26
    1re
    a1i
    @10
    c1
    rexadd
    syl2anc
    oveq1d
    @26
    @39
    cB
    @12
    cxad
    @26
    @0
    @39
    cB
    wceq
    @46
    cB
    xmulid2
    syl
    oveq2d
    3eqtr3d
    3eqtr4d
    exp31
    @0
    @30
    @13
    @17
    @0
    @30
    wa
    #
    @13
    wa
    @11
    cxne
    #
    @12
    cxne
    #
    @15
    @16
    @13
    @50
    @51
    wceq
    @49
    @11
    @12
    xnegeq
    adantl
    @49
    @15
    @50
    wceq
    @13
    @49
    @15
    @11
    cxrs
    cminusg
    cfv
    #
    cfv
    #
    @50
    @30
    @0
    @15
    @53
    wceq
    cxr
    @1
    cxrs
    @52
    @10
    cB
    xrsbas
    @22
    @52
    eqid
    mulgnegnn
    ancoms
    @49
    @11
    cxr
    wcel
    #
    @53
    @50
    wceq
    @30
    @0
    @54
    @30
    @0
    @54
    @30
    vx
    vy
    cxr
    cxad
    cxr
    @1
    cxrs
    @10
    cvv
    cB
    xrsbas
    @22
    xrsadd
    cxrs
    cvv
    wcel
    @30
    xrsex
    a1i
    cxr
    cxr
    wss
    @30
    cxr
    ssid
    a1i
    @30
    vx
    cv
    #
    cxr
    wcel
    #
    vy
    cv
    #
    cxr
    wcel
    #
    w3a
    @55
    @57
    @30
    @56
    @58
    simp2
    @30
    @56
    @58
    simp3
    xaddcld
    mulgnnsubcl
    3anidm12
    ancoms
    @11
    xrsinvgval
    syl
    eqtrd
    adantr
    @49
    @16
    @51
    wceq
    @13
    @49
    @10
    cxne
    #
    cB
    cxmu
    co
    #
    @16
    @51
    @49
    @59
    @14
    cB
    cxmu
    @49
    @47
    @59
    @14
    wceq
    @30
    @47
    @0
    @10
    nnre
    adantl
    @10
    rexneg
    syl
    oveq1d
    @49
    @41
    @0
    @60
    @51
    wceq
    @49
    cn
    cxr
    @10
    cn
    cr
    cxr
    nnssre
    ressxr
    sstri
    @0
    @30
    simpr
    sseldi
    @0
    @30
    simpl
    @10
    cB
    xmulneg1
    syl2anc
    eqtr3d
    adantr
    3eqtr4d
    exp31
    zindd
    impcom
end
