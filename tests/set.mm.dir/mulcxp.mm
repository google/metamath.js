include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "ccxp.mm"
include "wceq.mm"
include "simp1l.mm"
include "recnd.mm"
include "mul01d.mm"
include "oveq1d.mm"
include "simp3.mm"
include "mulcxplem.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "wi.mm"
include "simp2l.mm"
include "mul02d.mm"
include "cxpcl.mm"
include "syl2anc.mm"
include "0cn.mm"
include "sylancr.mm"
include "mulcomd.mm"
include "a1dd.mm"
include "clog.mm"
include "cfv.mm"
include "ce.mm"
include "caddc.mm"
include "adantr.mm"
include "simpl1r.mm"
include "simprl.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "simpl2r.mm"
include "simprr.mm"
include "relogmuld.mm"
include "logcld.mm"
include "adddid.mm"
include "fveq2d.mm"
include "mulcld.mm"
include "efadd.mm"
include "mulne0d.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "exp32.mm"
include "pm2.61dne.mm"

theorem mulcxp
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) /\ C e. CC ) -> ( ( A x. B ) ^c C ) = ( ( A ^c C ) x. ( B ^c C ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cB
    cmul
    co
    #
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
    cmul
    co
    #
    wceq
    #
    cB
    cc0
    @7
    @13
    cB
    cc0
    wceq
    #
    cA
    cc0
    cmul
    co
    #
    cC
    ccxp
    co
    #
    @10
    cc0
    cC
    ccxp
    co
    #
    cmul
    co
    #
    wceq
    @7
    @16
    @17
    @18
    @7
    @15
    cc0
    cC
    ccxp
    @7
    cA
    @7
    cA
    @0
    @1
    @5
    @6
    simp1l
    #
    recnd
    #
    mul01d
    oveq1d
    @7
    cA
    cC
    @20
    @2
    @5
    @6
    simp3
    #
    mulcxplem
    eqtrd
    @14
    @9
    @16
    @12
    @18
    @14
    @8
    @15
    cC
    ccxp
    cB
    cc0
    cA
    cmul
    oveq2
    oveq1d
    @14
    @11
    @17
    @10
    cmul
    cB
    cc0
    cC
    ccxp
    oveq1
    oveq2d
    eqeq12d
    syl5ibrcom
    @7
    cB
    cc0
    wne
    #
    @13
    wi
    cA
    cc0
    @7
    cA
    cc0
    wceq
    #
    @13
    @22
    @7
    @13
    @23
    cc0
    cB
    cmul
    co
    #
    cC
    ccxp
    co
    #
    @17
    @11
    cmul
    co
    #
    wceq
    @7
    @25
    @17
    @26
    @7
    @24
    cc0
    cC
    ccxp
    @7
    cB
    @7
    cB
    @2
    @3
    @4
    @6
    simp2l
    #
    recnd
    #
    mul02d
    oveq1d
    @7
    @17
    @11
    @17
    cmul
    co
    @26
    @7
    cB
    cC
    @28
    @21
    mulcxplem
    @7
    @11
    @17
    @7
    cB
    cc
    wcel
    #
    @6
    @11
    cc
    wcel
    @28
    @21
    cB
    cC
    cxpcl
    syl2anc
    @7
    cc0
    cc
    wcel
    @6
    @17
    cc
    wcel
    0cn
    @21
    cc0
    cC
    cxpcl
    sylancr
    mulcomd
    eqtrd
    eqtrd
    @23
    @9
    @25
    @12
    @26
    @23
    @8
    @24
    cC
    ccxp
    cA
    cc0
    cB
    cmul
    oveq1
    oveq1d
    @23
    @10
    @17
    @11
    cmul
    cA
    cc0
    cC
    ccxp
    oveq1
    oveq1d
    eqeq12d
    syl5ibrcom
    a1dd
    @7
    cA
    cc0
    wne
    #
    @22
    @13
    @7
    @30
    @22
    wa
    #
    wa
    #
    cC
    @8
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cC
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cC
    cB
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    @9
    @12
    @32
    @35
    @37
    @40
    caddc
    co
    #
    ce
    cfv
    #
    @42
    @32
    @34
    @43
    ce
    @32
    @34
    cC
    @36
    @39
    caddc
    co
    #
    cmul
    co
    @43
    @32
    @33
    @45
    cC
    cmul
    @32
    cA
    cB
    @32
    cA
    @7
    @0
    @31
    @19
    adantr
    #
    @32
    cA
    @46
    @0
    @1
    @5
    @6
    @31
    simpl1r
    @7
    @30
    @22
    simprl
    #
    ne0gt0d
    elrpd
    @32
    cB
    @7
    @3
    @31
    @27
    adantr
    #
    @32
    cB
    @48
    @3
    @4
    @2
    @6
    @31
    simpl2r
    @7
    @30
    @22
    simprr
    #
    ne0gt0d
    elrpd
    relogmuld
    oveq2d
    @32
    cC
    @36
    @39
    @7
    @6
    @31
    @21
    adantr
    #
    @32
    cA
    @7
    cA
    cc
    wcel
    #
    @31
    @20
    adantr
    #
    @47
    logcld
    #
    @32
    cB
    @7
    @29
    @31
    @28
    adantr
    #
    @49
    logcld
    #
    adddid
    eqtrd
    fveq2d
    @32
    @37
    cc
    wcel
    @40
    cc
    wcel
    @44
    @42
    wceq
    @32
    cC
    @36
    @50
    @53
    mulcld
    @32
    cC
    @39
    @50
    @55
    mulcld
    @37
    @40
    efadd
    syl2anc
    eqtrd
    @32
    @8
    cc
    wcel
    @8
    cc0
    wne
    @6
    @9
    @35
    wceq
    @32
    cA
    cB
    @52
    @54
    mulcld
    @32
    cA
    cB
    @52
    @54
    @47
    @49
    mulne0d
    @50
    @8
    cC
    cxpef
    syl3anc
    @32
    @10
    @38
    @11
    @41
    cmul
    @32
    @51
    @30
    @6
    @10
    @38
    wceq
    @52
    @47
    @50
    cA
    cC
    cxpef
    syl3anc
    @32
    @29
    @22
    @6
    @11
    @41
    wceq
    @54
    @49
    @50
    cB
    cC
    cxpef
    syl3anc
    oveq12d
    3eqtr4d
    exp32
    pm2.61dne
    pm2.61dne
end
