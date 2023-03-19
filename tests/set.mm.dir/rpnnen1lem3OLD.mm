include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "crn.mm"
include "wral.mm"
include "cn.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "nnex.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "fveq1d.mm"
include "ovex.mm"
include "eqid.mm"
include "sylan9eq.mm"
include "cmul.mm"
include "cz.mm"
include "rabeq2i.mm"
include "cc0.mm"
include "wb.mm"
include "zre.mm"
include "adantl.mm"
include "simpll.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "ad2antlr.mm"
include "ltdivmul.mm"
include "syl3anc.mm"
include "wi.mm"
include "remulcl.mm"
include "syl2anc.mm"
include "ltle.mm"
include "sylbid.mm"
include "impr.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "ancoms.mm"
include "sylan2.mm"
include "btwnz.mm"
include "simpld.mm"
include "syl.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "rabn0.mm"
include "sylibr.mm"
include "neeq1i.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "rpnnen1lem2.mm"
include "zred.mm"
include "simpl.mm"
include "ledivmul.mm"
include "eqbrtrd.mm"
include "cq.mm"
include "wf.mm"
include "wfn.mm"
include "cmap.mm"
include "rpnnen1lem1OLD.mm"
include "qex.mm"
include "elmap.mm"
include "sylib.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "3syl.mm"

theorem rpnnen1lem3OLD
  let vx: setvar x
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume rpnnen1.1OLD: |- T = { n e. ZZ | ( n / k ) < x }
  assume rpnnen1.2OLD: |- F = ( x e. RR |-> ( k e. NN |-> ( sup ( T , RR , < ) / k ) ) )

  disjoint F k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint T n
  disjoint F y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint T y
  assert |- ( x e. RR -> A. n e. ran ( F ` x ) n <_ x )

  proof
    vx
    cv
    #
    cr
    wcel
    #
    vn
    cv
    #
    @0
    cle
    wbr
    #
    vn
    @0
    cF
    cfv
    #
    crn
    wral
    #
    vk
    cv
    #
    @4
    cfv
    #
    @0
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @1
    @8
    vk
    cn
    @1
    @6
    cn
    wcel
    #
    wa
    #
    @7
    cT
    cr
    clt
    csup
    #
    @6
    cdiv
    co
    #
    @0
    cle
    @1
    @10
    @7
    @6
    vk
    cn
    @13
    cmpt
    #
    cfv
    #
    @13
    @1
    @6
    @4
    @14
    @1
    @14
    cvv
    wcel
    @4
    @14
    wceq
    vk
    cn
    @13
    nnex
    mptex
    vx
    cr
    @14
    cvv
    cF
    rpnnen1.2OLD
    fvmpt2
    mpan2
    fveq1d
    @10
    @13
    cvv
    wcel
    @15
    @13
    wceq
    @12
    @6
    cdiv
    ovex
    vk
    cn
    @13
    cvv
    @14
    @14
    eqid
    fvmpt2
    mpan2
    sylan9eq
    @11
    @13
    @0
    cle
    wbr
    #
    @12
    @6
    @0
    cmul
    co
    #
    cle
    wbr
    #
    @11
    @18
    @2
    @17
    cle
    wbr
    #
    vn
    cT
    wral
    #
    @11
    @19
    vn
    cT
    @2
    cT
    wcel
    @11
    @2
    cz
    wcel
    #
    @2
    @6
    cdiv
    co
    @0
    clt
    wbr
    #
    wa
    @19
    @22
    vn
    cT
    cz
    rpnnen1.1OLD
    rabeq2i
    @11
    @21
    @22
    @19
    @11
    @21
    wa
    #
    @22
    @2
    @17
    clt
    wbr
    #
    @19
    @23
    @2
    cr
    wcel
    #
    @1
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    wa
    #
    @22
    @24
    wb
    @21
    @25
    @11
    @2
    zre
    adantl
    #
    @1
    @10
    @21
    simpll
    #
    @10
    @28
    @1
    @21
    @10
    @26
    @27
    @6
    nnre
    #
    @6
    nngt0
    jca
    #
    ad2antlr
    @2
    @0
    @6
    ltdivmul
    syl3anc
    #
    @23
    @25
    @17
    cr
    wcel
    #
    @24
    @19
    wi
    @29
    @23
    @26
    @1
    @34
    @10
    @26
    @1
    @21
    @31
    ad2antlr
    @30
    @6
    @0
    remulcl
    #
    syl2anc
    @2
    @17
    ltle
    syl2anc
    sylbid
    impr
    sylan2b
    ralrimiva
    #
    @11
    cT
    cr
    wss
    #
    cT
    c0
    wne
    #
    @2
    vy
    cv
    #
    cle
    wbr
    #
    vn
    cT
    wral
    #
    vy
    cr
    wrex
    #
    @34
    @18
    @20
    wb
    @37
    @11
    cT
    cz
    cr
    cT
    @22
    vn
    cz
    crab
    #
    cz
    rpnnen1.1OLD
    @22
    vn
    cz
    ssrab2
    eqsstri
    zssre
    sstri
    a1i
    @11
    @43
    c0
    wne
    #
    @38
    @11
    @22
    vn
    cz
    wrex
    #
    @44
    @11
    @45
    @24
    vn
    cz
    wrex
    #
    @11
    @34
    @46
    @10
    @1
    @26
    @34
    @31
    @26
    @1
    @34
    @35
    ancoms
    sylan2
    #
    @34
    @46
    @17
    @2
    clt
    wbr
    vn
    cz
    wrex
    vn
    vn
    @17
    btwnz
    simpld
    syl
    @11
    @22
    @24
    vn
    cz
    @33
    rexbidva
    mpbird
    @22
    vn
    cz
    rabn0
    sylibr
    cT
    @43
    c0
    rpnnen1.1OLD
    neeq1i
    sylibr
    @11
    @34
    @20
    @42
    @47
    @36
    @41
    @20
    vy
    @17
    cr
    @39
    @17
    wceq
    @40
    @19
    vn
    cT
    @39
    @17
    @2
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    @47
    vy
    vn
    vn
    cT
    @17
    suprleub
    syl31anc
    mpbird
    @11
    @12
    cr
    wcel
    @1
    @28
    @16
    @18
    wb
    @11
    @12
    vx
    cT
    vk
    vn
    cF
    rpnnen1.1OLD
    rpnnen1.2OLD
    rpnnen1lem2
    zred
    @1
    @10
    simpl
    @10
    @28
    @1
    @32
    adantl
    @12
    @0
    @6
    ledivmul
    syl3anc
    mpbird
    eqbrtrd
    ralrimiva
    @1
    cn
    cq
    @4
    wf
    #
    @4
    cn
    wfn
    @5
    @9
    wb
    @1
    @4
    cq
    cn
    cmap
    co
    wcel
    @48
    vx
    cT
    vk
    vn
    cF
    rpnnen1.1OLD
    rpnnen1.2OLD
    rpnnen1lem1OLD
    cq
    cn
    @4
    qex
    nnex
    elmap
    sylib
    cn
    cq
    @4
    ffn
    @3
    @8
    vn
    vk
    cn
    @4
    @2
    @7
    @0
    cle
    breq1
    ralrn
    3syl
    mpbird
end
