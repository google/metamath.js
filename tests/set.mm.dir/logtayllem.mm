include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cif.mm"
include "cmul.mm"
include "nn0uz.mm"
include "1nn0.mm"
include "a1i.mm"
include "cr.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "abscl.mm"
include "adantr.mm"
include "reexpcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "oveq12d.mm"
include "0cnd.mm"
include "wne.mm"
include "wn.mm"
include "nn0cn.mm"
include "df-ne.mm"
include "biimpri.mm"
include "reccl.mm"
include "syl2an.mm"
include "ifclda.mm"
include "expcl.mm"
include "adantlr.mm"
include "mulcld.mm"
include "caddc.mm"
include "cseq.mm"
include "cmin.mm"
include "cli.mm"
include "cdm.mm"
include "recnd.mm"
include "absidm.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "geolim.mm"
include "seqex.mm"
include "breldm.mm"
include "syl.mm"
include "1red.mm"
include "cuz.mm"
include "cn.mm"
include "cle.mm"
include "elnnuz.mm"
include "nnrecre.mm"
include "nnnn0.mm"
include "sylan2.mm"
include "absmuld.mm"
include "crp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "absidd.mm"
include "simpl.mm"
include "absexp.mm"
include "eqtrd.mm"
include "absge0d.mm"
include "breqtrd.mm"
include "nnge1.mm"
include "wb.mm"
include "0lt1.mm"
include "nnre.mm"
include "nngt0.mm"
include "lerec.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "1div1e1.mm"
include "syl6breq.mm"
include "lemul1ad.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3brtr4d.mm"
include "sylan2br.mm"
include "cvgcmpce.mm"

theorem logtayllem
  let cA: class A
  let vn: setvar n
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S

  disjoint A n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint S n
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> seq 0 ( + , ( n e. NN0 |-> ( if ( n = 0 , 0 , ( 1 / n ) ) x. ( A ^ n ) ) ) ) e. dom ~~> )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    c1
    vk
    vn
    cn0
    @1
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    vn
    cn0
    @4
    cc0
    wceq
    #
    cc0
    c1
    @4
    cdiv
    co
    #
    cif
    #
    cA
    @4
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    c1
    cn0
    nn0uz
    c1
    cn0
    wcel
    @3
    1nn0
    a1i
    @3
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @13
    @6
    cfv
    #
    @1
    @13
    cexp
    co
    #
    cr
    @14
    @16
    @17
    wceq
    #
    @3
    vn
    @13
    @5
    @17
    cn0
    @6
    @4
    @13
    @1
    cexp
    oveq2
    @6
    eqid
    @1
    @13
    cexp
    ovex
    fvmpt
    adantl
    #
    @3
    @1
    cr
    wcel
    #
    @14
    @17
    cr
    wcel
    #
    @0
    @20
    @2
    cA
    abscl
    adantr
    #
    @1
    @13
    reexpcl
    sylan
    #
    eqeltrd
    @15
    @13
    @12
    cfv
    #
    @13
    cc0
    wceq
    #
    cc0
    c1
    @13
    cdiv
    co
    #
    cif
    #
    cA
    @13
    cexp
    co
    #
    cmul
    co
    #
    cc
    @14
    @24
    @29
    wceq
    #
    @3
    vn
    @13
    @11
    @29
    cn0
    @12
    @4
    @13
    wceq
    #
    @9
    @27
    @10
    @28
    cmul
    @31
    @7
    @25
    @8
    @26
    cc0
    @4
    @13
    cc0
    eqeq1
    @4
    @13
    c1
    cdiv
    oveq2
    ifbieq2d
    @4
    @13
    cA
    cexp
    oveq2
    oveq12d
    @12
    eqid
    @27
    @28
    cmul
    ovex
    fvmpt
    adantl
    #
    @15
    @27
    @28
    @15
    @25
    cc0
    @26
    cc
    @15
    @25
    wa
    0cnd
    @15
    @13
    cc
    wcel
    #
    @13
    cc0
    wne
    #
    @26
    cc
    wcel
    @25
    wn
    #
    @14
    @33
    @3
    @13
    nn0cn
    adantl
    @34
    @35
    @13
    cc0
    df-ne
    biimpri
    @13
    reccl
    syl2an
    ifclda
    @0
    @14
    @28
    cc
    wcel
    #
    @2
    cA
    @13
    expcl
    adantlr
    #
    mulcld
    eqeltrd
    @3
    caddc
    @6
    cc0
    cseq
    #
    c1
    c1
    @1
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wbr
    @38
    cli
    cdm
    wcel
    @3
    @1
    vk
    @6
    @3
    @1
    @22
    recnd
    @3
    @1
    cabs
    cfv
    #
    @1
    c1
    clt
    @0
    @41
    @1
    wceq
    @2
    cA
    absidm
    adantr
    @0
    @2
    simpr
    eqbrtrd
    @19
    geolim
    @38
    @40
    cli
    caddc
    @6
    cc0
    seqex
    c1
    @39
    cdiv
    ovex
    breldm
    syl
    @3
    1red
    @13
    c1
    cuz
    cfv
    wcel
    @3
    @13
    cn
    wcel
    #
    @24
    cabs
    cfv
    #
    c1
    @16
    cmul
    co
    #
    cle
    wbr
    @13
    elnnuz
    @3
    @42
    wa
    #
    @26
    @28
    cmul
    co
    #
    cabs
    cfv
    #
    c1
    @17
    cmul
    co
    #
    @43
    @44
    cle
    @45
    @47
    @26
    @17
    cmul
    co
    #
    @48
    cle
    @45
    @47
    @26
    cabs
    cfv
    #
    @28
    cabs
    cfv
    #
    cmul
    co
    @49
    @45
    @26
    @28
    @45
    @26
    @42
    @26
    cr
    wcel
    @3
    @13
    nnrecre
    adantl
    #
    recnd
    @42
    @3
    @14
    @36
    @13
    nnnn0
    #
    @37
    sylan2
    #
    absmuld
    @45
    @50
    @26
    @51
    @17
    cmul
    @45
    @26
    @52
    @45
    @26
    @45
    @13
    @42
    @13
    crp
    wcel
    @3
    @13
    nnrp
    adantl
    rpreccld
    rpge0d
    absidd
    @3
    @0
    @14
    @51
    @17
    wceq
    @42
    @0
    @2
    simpl
    @53
    cA
    @13
    absexp
    syl2an
    #
    oveq12d
    eqtrd
    @45
    @26
    c1
    @17
    @52
    @45
    1red
    #
    @42
    @3
    @14
    @21
    @53
    @23
    sylan2
    @45
    cc0
    @51
    @17
    cle
    @45
    @28
    @54
    absge0d
    @55
    breqtrd
    @45
    @26
    c1
    c1
    cdiv
    co
    #
    c1
    cle
    @45
    c1
    @13
    cle
    wbr
    #
    @26
    @57
    cle
    wbr
    #
    @42
    @58
    @3
    @13
    nnge1
    adantl
    @45
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @13
    cr
    wcel
    #
    cc0
    @13
    clt
    wbr
    #
    @58
    @59
    wb
    @56
    @60
    @45
    0lt1
    a1i
    @42
    @61
    @3
    @13
    nnre
    adantl
    @42
    @62
    @3
    @13
    nngt0
    adantl
    c1
    @13
    lerec
    syl22anc
    mpbid
    1div1e1
    syl6breq
    lemul1ad
    eqbrtrd
    @45
    @24
    @46
    cabs
    @45
    @24
    @29
    @46
    @42
    @3
    @14
    @30
    @53
    @32
    sylan2
    @45
    @27
    @26
    @28
    cmul
    @45
    @25
    cc0
    @26
    @45
    @13
    cc0
    @42
    @34
    @3
    @13
    nnne0
    adantl
    neneqd
    iffalsed
    oveq1d
    eqtrd
    fveq2d
    @45
    @16
    @17
    c1
    cmul
    @42
    @3
    @14
    @18
    @53
    @19
    sylan2
    oveq2d
    3brtr4d
    sylan2br
    cvgcmpce
end
