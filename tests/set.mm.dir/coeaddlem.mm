include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "wceq.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cc.mm"
include "plyaddcl.mm"
include "cn0.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "adantl.mm"
include "adantr.mm"
include "ifcld.mm"
include "cvv.mm"
include "cv.mm"
include "addcl.mm"
include "wf.mm"
include "coef3.mm"
include "nn0ex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "c1.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wo.mm"
include "wn.mm"
include "oveq12.mm"
include "00id.mm"
include "syl6eq.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "eqidd.mm"
include "ofval.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "necon3ad.mm"
include "neorian.mm"
include "syl6ibr.mm"
include "dgrub2.mm"
include "wb.mm"
include "plyco0.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "cr.mm"
include "nn0red.mm"
include "max1.mm"
include "nn0re.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syld.mm"
include "max2.mm"
include "jaod.mm"
include "ralrimiva.mm"
include "mpbird.mm"
include "simpl.mm"
include "simpr.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "coeid.mm"
include "plyaddlem1.mm"
include "coeeq.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "dgrle.mm"
include "jca.mm"

theorem coeaddlem
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume coefv0.1: |- A = ( coeff ` F )
  assume coeadd.2: |- B = ( coeff ` G )
  assume coeadd.3: |- M = ( deg ` F )
  assume coeadd.4: |- N = ( deg ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( ( coeff ` ( F oF + G ) ) = ( A oF + B ) /\ ( deg ` ( F oF + G ) ) <_ if ( M <_ N , N , M ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    caddc
    cof
    #
    co
    #
    ccoe
    cfv
    cA
    cB
    @4
    co
    #
    wceq
    @5
    cdgr
    cfv
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cle
    wbr
    @3
    vz
    @6
    cc
    vk
    @5
    @8
    cS
    cF
    cG
    plyaddcl
    #
    @3
    @7
    cN
    cM
    cn0
    @2
    cN
    cn0
    wcel
    #
    @1
    @2
    cN
    cG
    cdgr
    cfv
    cn0
    coeadd.4
    cS
    cG
    dgrcl
    syl5eqel
    adantl
    #
    @1
    cM
    cn0
    wcel
    #
    @2
    @1
    cM
    cF
    cdgr
    cfv
    cn0
    coeadd.3
    cS
    cF
    dgrcl
    syl5eqel
    adantr
    #
    ifcld
    #
    @3
    vx
    vy
    cn0
    cn0
    cn0
    caddc
    cc
    cc
    cc
    cA
    cB
    cvv
    cvv
    vx
    cv
    #
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @15
    @16
    caddc
    co
    cc
    wcel
    @3
    @15
    @16
    addcl
    adantl
    @1
    cn0
    cc
    cA
    wf
    #
    @2
    cA
    cS
    cF
    coefv0.1
    coef3
    adantr
    #
    @2
    cn0
    cc
    cB
    wf
    #
    @1
    cB
    cS
    cG
    coeadd.2
    coef3
    adantl
    #
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    #
    @21
    cn0
    inidm
    #
    off
    #
    @3
    @6
    @8
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    #
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
    @26
    @8
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @3
    @30
    vk
    cn0
    @3
    @26
    cn0
    wcel
    #
    wa
    #
    @28
    @26
    cA
    cfv
    #
    cc0
    wne
    #
    @26
    cB
    cfv
    #
    cc0
    wne
    #
    wo
    #
    @29
    @33
    @28
    @34
    cc0
    wceq
    @36
    cc0
    wceq
    wa
    #
    wn
    @38
    @33
    @39
    @27
    cc0
    @39
    @27
    cc0
    wceq
    @33
    @34
    @36
    caddc
    co
    #
    cc0
    wceq
    @39
    @40
    cc0
    cc0
    caddc
    co
    cc0
    @34
    cc0
    @36
    cc0
    caddc
    oveq12
    00id
    syl6eq
    @33
    @27
    @40
    cc0
    @3
    cn0
    cn0
    @34
    @36
    caddc
    cn0
    cA
    cB
    cvv
    cvv
    @26
    @3
    @17
    cA
    cn0
    wfn
    @18
    cn0
    cc
    cA
    ffn
    syl
    @3
    @19
    cB
    cn0
    wfn
    @20
    cn0
    cc
    cB
    ffn
    syl
    @21
    @21
    @22
    @33
    @34
    eqidd
    @33
    @36
    eqidd
    ofval
    eqeq1d
    syl5ibr
    necon3ad
    @34
    cc0
    @36
    cc0
    neorian
    syl6ibr
    @33
    @35
    @29
    @37
    @33
    @35
    @26
    cM
    cle
    wbr
    #
    @29
    @3
    @35
    @41
    wi
    #
    vk
    cn0
    @3
    cA
    cM
    c1
    caddc
    co
    cuz
    cfv
    cima
    @24
    wceq
    #
    @42
    vk
    cn0
    wral
    #
    @1
    @43
    @2
    cA
    cS
    cF
    cM
    coefv0.1
    coeadd.3
    dgrub2
    adantr
    #
    @3
    @12
    @17
    @43
    @44
    wb
    @13
    @18
    cA
    vk
    cM
    plyco0
    syl2anc
    mpbid
    r19.21bi
    @33
    @41
    cM
    @8
    cle
    wbr
    #
    @29
    @33
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @46
    @33
    cM
    @3
    @12
    @32
    @13
    adantr
    nn0red
    #
    @33
    cN
    @3
    @10
    @32
    @11
    adantr
    nn0red
    #
    cM
    cN
    max1
    syl2anc
    @33
    @26
    cr
    wcel
    #
    @47
    @8
    cr
    wcel
    #
    @41
    @46
    wa
    @29
    wi
    @32
    @51
    @3
    @26
    nn0re
    adantl
    #
    @49
    @33
    @8
    @3
    @8
    cn0
    wcel
    #
    @32
    @14
    adantr
    nn0red
    #
    @26
    cM
    @8
    letr
    syl3anc
    mpan2d
    syld
    @33
    @37
    @26
    cN
    cle
    wbr
    #
    @29
    @3
    @37
    @56
    wi
    #
    vk
    cn0
    @3
    cB
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    @24
    wceq
    #
    @57
    vk
    cn0
    wral
    #
    @2
    @58
    @1
    cB
    cS
    cG
    cN
    coeadd.2
    coeadd.4
    dgrub2
    adantl
    #
    @3
    @10
    @19
    @58
    @59
    wb
    @11
    @20
    cB
    vk
    cN
    plyco0
    syl2anc
    mpbid
    r19.21bi
    @33
    @56
    cN
    @8
    cle
    wbr
    #
    @29
    @33
    @47
    @48
    @61
    @49
    @50
    cM
    cN
    max2
    syl2anc
    @33
    @51
    @48
    @52
    @56
    @61
    wa
    @29
    wi
    @53
    @50
    @55
    @26
    cN
    @8
    letr
    syl3anc
    mpan2d
    syld
    jaod
    syld
    ralrimiva
    @3
    @54
    cn0
    cc
    @6
    wf
    #
    @25
    @31
    wb
    @14
    @23
    @6
    vk
    @8
    plyco0
    syl2anc
    mpbird
    @3
    vz
    cA
    cB
    cS
    vk
    cF
    cG
    cM
    cN
    @1
    @2
    simpl
    @1
    @2
    simpr
    @13
    @11
    @18
    @20
    @45
    @60
    @1
    cF
    vz
    cc
    cc0
    cM
    cfz
    co
    @34
    vz
    cv
    @26
    cexp
    co
    #
    cmul
    co
    vk
    csu
    cmpt
    wceq
    @2
    vz
    cA
    cS
    vk
    cF
    cM
    coefv0.1
    coeadd.3
    coeid
    adantr
    @2
    cG
    vz
    cc
    cc0
    cN
    cfz
    co
    @36
    @63
    cmul
    co
    vk
    csu
    cmpt
    wceq
    @1
    vz
    cB
    cS
    vk
    cG
    cN
    coeadd.2
    coeadd.4
    coeid
    adantl
    plyaddlem1
    #
    coeeq
    @3
    vz
    @27
    cc
    vk
    @5
    @8
    @9
    @14
    @3
    @62
    @32
    @27
    cc
    wcel
    @26
    cc0
    @8
    cfz
    co
    wcel
    @23
    @26
    @8
    elfznn0
    cn0
    cc
    @26
    @6
    ffvelrn
    syl2an
    @64
    dgrle
    jca
end
