include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "ccoe.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "wne.mm"
include "cdgr.mm"
include "wi.mm"
include "wss.mm"
include "cply.mm"
include "ssid.mm"
include "ply1term.mm"
include "mp3an1.mm"
include "simpr.mm"
include "simpl.mm"
include "0cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "csn.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "neeq1d.mm"
include "nn0re.mm"
include "leidd.mm"
include "ad2antlr.mm"
include "iffalse.mm"
include "necon1ai.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "wf.mm"
include "wb.mm"
include "plyco0.mm"
include "mpbird.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "ply1termlem.mm"
include "elfznn0.mm"
include "oveq1d.mm"
include "sylan2.mm"
include "sumeq2dv.mm"
include "mpteq2dv.mm"
include "eqtr4d.mm"
include "coeeq.mm"
include "iftrue.mm"
include "ancoms.mm"
include "biimpar.mm"
include "dgreq.mm"
include "ex.mm"
include "jca.mm"

theorem coe1termlem
  let vz: setvar z
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vk: setvar k
  let cM: class M
  assume coe1term.1: |- F = ( z e. CC |-> ( A x. ( z ^ N ) ) )

  disjoint n z
  disjoint A n
  disjoint A z
  disjoint N n
  disjoint N z
  disjoint k n
  disjoint k z
  disjoint A k
  disjoint M n
  disjoint N k
  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( ( coeff ` F ) = ( n e. NN0 |-> if ( n = N , A , 0 ) ) /\ ( A =/= 0 -> ( deg ` F ) = N ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cF
    ccoe
    cfv
    vn
    cn0
    vn
    cv
    #
    cN
    wceq
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    wceq
    cA
    cc0
    wne
    #
    cF
    cdgr
    cfv
    cN
    wceq
    #
    wi
    @2
    vz
    @6
    cc
    vk
    cF
    cN
    cc
    cc
    wss
    @0
    @1
    cF
    cc
    cply
    cfv
    wcel
    #
    cc
    ssid
    vz
    cA
    cc
    cF
    cN
    coe1term.1
    ply1term
    mp3an1
    #
    @0
    @1
    simpr
    #
    @2
    vn
    cn0
    @5
    cc
    @6
    @2
    @5
    cc
    wcel
    #
    @3
    cn0
    wcel
    @2
    @0
    cc0
    cc
    wcel
    #
    @12
    @0
    @1
    simpl
    #
    0cn
    @4
    cA
    cc0
    cc
    ifcl
    sylancl
    adantr
    @6
    eqid
    #
    fmptd
    #
    @2
    @6
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    wceq
    #
    vk
    cv
    #
    @6
    cfv
    #
    cc0
    wne
    #
    @18
    cN
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @2
    @22
    vk
    cn0
    @2
    @18
    cn0
    wcel
    #
    wa
    #
    @20
    @18
    cN
    wceq
    #
    cA
    cc0
    cif
    #
    cc0
    wne
    #
    @21
    @25
    @19
    @27
    cc0
    @25
    @24
    @27
    cc
    wcel
    #
    @19
    @27
    wceq
    @2
    @24
    simpr
    @2
    @29
    @24
    @2
    @0
    @13
    @29
    @14
    0cn
    @26
    cA
    cc0
    cc
    ifcl
    sylancl
    adantr
    vn
    @18
    @5
    @27
    cn0
    cc
    @6
    @3
    @18
    wceq
    @4
    @26
    cA
    cc0
    @3
    @18
    cN
    eqeq1
    ifbid
    @15
    fvmptg
    syl2anc
    #
    neeq1d
    @25
    @21
    @28
    cN
    cN
    cle
    wbr
    #
    @1
    @31
    @0
    @24
    @1
    cN
    cN
    nn0re
    leidd
    ad2antlr
    @28
    @18
    cN
    cN
    cle
    @26
    @27
    cc0
    @26
    cA
    cc0
    iffalse
    necon1ai
    breq1d
    syl5ibrcom
    sylbid
    ralrimiva
    @2
    @1
    cn0
    cc
    @6
    wf
    #
    @17
    @23
    wb
    @11
    @16
    @6
    vk
    cN
    plyco0
    syl2anc
    mpbird
    #
    @2
    cF
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    @27
    vz
    cv
    @18
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    vz
    cc
    @34
    @19
    @35
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    vz
    cA
    vk
    cF
    cN
    coe1term.1
    ply1termlem
    @2
    vz
    cc
    @39
    @37
    @2
    @34
    @38
    @36
    vk
    @18
    @34
    wcel
    @2
    @24
    @38
    @36
    wceq
    @18
    cN
    elfznn0
    @25
    @19
    @27
    @35
    cmul
    @30
    oveq1d
    sylan2
    sumeq2dv
    mpteq2dv
    eqtr4d
    #
    coeeq
    @2
    @7
    @8
    @2
    @7
    wa
    vz
    @6
    cc
    vk
    cF
    cN
    @2
    @9
    @7
    @10
    adantr
    @2
    @1
    @7
    @11
    adantr
    @2
    @32
    @7
    @16
    adantr
    @2
    @17
    @7
    @33
    adantr
    @2
    cF
    @40
    wceq
    @7
    @41
    adantr
    @2
    cN
    @6
    cfv
    #
    cc0
    wne
    @7
    @2
    @42
    cA
    cc0
    @1
    @0
    @42
    cA
    wceq
    vn
    cN
    @5
    cA
    cn0
    cc
    @6
    @4
    cA
    cc0
    iftrue
    @15
    fvmptg
    ancoms
    neeq1d
    biimpar
    dgreq
    ex
    jca
end
