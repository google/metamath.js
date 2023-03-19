include "cmul.mm"
include "cc.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "mulid1.mm"
include "adantl.mm"
include "cn.mm"
include "cuz.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "nnabscl.mm"
include "syl2anc.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cle.mm"
include "wbr.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "mulne0d.mm"
include "abscld.mm"
include "absge0d.mm"
include "nnge1d.mm"
include "lemulge11d.mm"
include "absmuld.mm"
include "breqtrrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "cfz.mm"
include "wa.mm"
include "wf.mm"
include "lgsfcl3.mm"
include "syl3anc.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "mulcl.mm"
include "seqcl.mm"
include "caddc.mm"
include "cprime.mm"
include "clgs.mm"
include "cpc.mm"
include "cexp.mm"
include "cif.mm"
include "peano2nnd.mm"
include "elfzuz.mm"
include "eluznn.mm"
include "eleq1.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "ovex.mm"
include "1ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cq.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "zq.mm"
include "pcabs.mm"
include "cdvds.mm"
include "wn.mm"
include "clt.mm"
include "elfzle1.mm"
include "wb.mm"
include "elfzelz.mm"
include "zltp1le.mm"
include "mpbird.mm"
include "cr.mm"
include "adantr.mm"
include "zred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wi.mm"
include "prmz.mm"
include "dvdsle.mm"
include "mtod.mm"
include "pceq0.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "lgscl.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "syl6eq.mm"
include "seqid2.mm"

theorem lgsdilem2
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cP: class P
  let vp: setvar p
  assume lgsdilem2.1: |- ( ph -> A e. ZZ )
  assume lgsdilem2.2: |- ( ph -> M e. ZZ )
  assume lgsdilem2.3: |- ( ph -> N e. ZZ )
  assume lgsdilem2.4: |- ( ph -> M =/= 0 )
  assume lgsdilem2.5: |- ( ph -> N =/= 0 )
  assume lgsdilem2.6: |- F = ( n e. NN |-> if ( n e. Prime , ( ( A /L n ) ^ ( n pCnt M ) ) , 1 ) )

  disjoint M n
  disjoint A n
  disjoint N n
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F k
  disjoint F x
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint P x
  disjoint k ph
  disjoint ph x
  disjoint k p
  disjoint A k
  disjoint n p
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N p
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( seq 1 ( x. , F ) ` ( abs ` M ) ) = ( seq 1 ( x. , F ) ` ( abs ` ( M x. N ) ) ) )

  proof
    wph
    vk
    cmul
    cc
    cF
    cM
    cabs
    cfv
    #
    c1
    cM
    cN
    cmul
    co
    #
    cabs
    cfv
    #
    c1
    vk
    cv
    #
    cc
    wcel
    #
    @3
    c1
    cmul
    co
    @3
    wceq
    wph
    @3
    mulid1
    adantl
    wph
    @0
    cn
    c1
    cuz
    cfv
    wph
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    #
    @0
    cn
    wcel
    #
    lgsdilem2.2
    lgsdilem2.4
    cM
    nnabscl
    #
    syl2anc
    #
    nnuz
    syl6eleq
    #
    wph
    @0
    cz
    wcel
    #
    @2
    cz
    wcel
    @0
    @2
    cle
    wbr
    @2
    @0
    cuz
    cfv
    wcel
    wph
    @0
    @9
    nnzd
    #
    wph
    @2
    wph
    @1
    cz
    wcel
    @1
    cc0
    wne
    @2
    cn
    wcel
    wph
    cM
    cN
    lgsdilem2.2
    lgsdilem2.3
    zmulcld
    wph
    cM
    cN
    wph
    cM
    lgsdilem2.2
    zcnd
    #
    wph
    cN
    lgsdilem2.3
    zcnd
    #
    lgsdilem2.4
    lgsdilem2.5
    mulne0d
    @1
    nnabscl
    syl2anc
    nnzd
    wph
    @0
    @0
    cN
    cabs
    cfv
    #
    cmul
    co
    @2
    cle
    wph
    @0
    @15
    wph
    cM
    @13
    abscld
    #
    wph
    cN
    @14
    abscld
    wph
    cM
    @13
    absge0d
    wph
    @15
    wph
    cN
    cz
    wcel
    cN
    cc0
    wne
    @15
    cn
    wcel
    lgsdilem2.3
    lgsdilem2.5
    cN
    nnabscl
    syl2anc
    nnge1d
    lemulge11d
    wph
    cM
    cN
    @13
    @14
    absmuld
    breqtrrd
    @0
    @2
    eluz2
    syl3anbrc
    wph
    vk
    vx
    cmul
    cc
    cF
    c1
    @0
    @10
    wph
    @3
    c1
    @0
    cfz
    co
    wcel
    #
    wa
    @3
    cF
    cfv
    #
    wph
    cn
    cz
    cF
    wf
    #
    @3
    cn
    wcel
    #
    @18
    cz
    wcel
    @17
    wph
    cA
    cz
    wcel
    #
    @5
    @6
    @19
    lgsdilem2.1
    lgsdilem2.2
    lgsdilem2.4
    cA
    vn
    cF
    cM
    lgsdilem2.6
    lgsfcl3
    syl3anc
    @3
    @0
    elfznn
    cn
    cz
    @3
    cF
    ffvelrn
    syl2an
    zcnd
    @4
    vx
    cv
    #
    cc
    wcel
    wa
    @3
    @22
    cmul
    co
    cc
    wcel
    wph
    @3
    @22
    mulcl
    adantl
    seqcl
    wph
    @3
    @0
    c1
    caddc
    co
    #
    @2
    cfz
    co
    wcel
    #
    wa
    #
    @18
    @3
    cprime
    wcel
    #
    cA
    @3
    clgs
    co
    #
    @3
    cM
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    c1
    @25
    @20
    @18
    @30
    wceq
    wph
    @23
    cn
    wcel
    @3
    @23
    cuz
    cfv
    wcel
    @20
    @24
    wph
    @0
    @9
    peano2nnd
    @3
    @23
    @2
    elfzuz
    @3
    @23
    eluznn
    syl2an
    vn
    @3
    vn
    cv
    #
    cprime
    wcel
    #
    cA
    @31
    clgs
    co
    #
    @31
    cM
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    @30
    cn
    cF
    @31
    @3
    wceq
    #
    @32
    @26
    @35
    @29
    c1
    @31
    @3
    cprime
    eleq1
    @36
    @33
    @27
    @34
    @28
    cexp
    @31
    @3
    cA
    clgs
    oveq2
    @31
    @3
    cM
    cpc
    oveq1
    oveq12d
    ifbieq1d
    lgsdilem2.6
    @26
    @29
    c1
    @27
    @28
    cexp
    ovex
    1ex
    ifex
    fvmpt
    syl
    @25
    @30
    @26
    c1
    c1
    cif
    c1
    @25
    @26
    @29
    c1
    c1
    @25
    @26
    wa
    #
    @29
    @27
    cc0
    cexp
    co
    c1
    @37
    @28
    cc0
    @27
    cexp
    @37
    @3
    @0
    cpc
    co
    #
    @28
    cc0
    @37
    @26
    cM
    cq
    wcel
    #
    @38
    @28
    wceq
    @25
    @26
    simpr
    #
    @37
    @5
    @39
    wph
    @5
    @24
    @26
    lgsdilem2.2
    ad2antrr
    #
    cM
    zq
    syl
    cM
    @3
    pcabs
    syl2anc
    @37
    @38
    cc0
    wceq
    #
    @3
    @0
    cdvds
    wbr
    #
    wn
    #
    @37
    @43
    @3
    @0
    cle
    wbr
    #
    @25
    @45
    wn
    #
    @26
    @25
    @0
    @3
    clt
    wbr
    #
    @46
    @25
    @47
    @23
    @3
    cle
    wbr
    #
    @24
    @48
    wph
    @3
    @23
    @2
    elfzle1
    adantl
    wph
    @11
    @3
    cz
    wcel
    #
    @47
    @48
    wb
    @24
    @12
    @3
    @23
    @2
    elfzelz
    #
    @0
    @3
    zltp1le
    syl2an
    mpbird
    @25
    @0
    @3
    wph
    @0
    cr
    wcel
    @24
    @16
    adantr
    @25
    @3
    @24
    @49
    wph
    @50
    adantl
    zred
    ltnled
    mpbid
    adantr
    @37
    @49
    @7
    @43
    @45
    wi
    @26
    @49
    @25
    @3
    prmz
    adantl
    #
    @37
    @5
    @6
    @7
    @41
    wph
    @6
    @24
    @26
    lgsdilem2.4
    ad2antrr
    @8
    syl2anc
    #
    @3
    @0
    dvdsle
    syl2anc
    mtod
    @37
    @26
    @7
    @42
    @44
    wb
    @40
    @52
    @3
    @0
    pceq0
    syl2anc
    mpbird
    eqtr3d
    oveq2d
    @37
    @27
    @37
    @27
    @37
    @21
    @49
    @27
    cz
    wcel
    wph
    @21
    @24
    @26
    lgsdilem2.1
    ad2antrr
    @51
    cA
    @3
    lgscl
    syl2anc
    zcnd
    exp0d
    eqtrd
    ifeq1da
    @26
    c1
    ifid
    syl6eq
    eqtrd
    seqid2
end
