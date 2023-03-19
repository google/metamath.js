include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "ccj.mm"
include "cmul.mm"
include "cre.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "simpl.mm"
include "simpr.mm"
include "cjcld.mm"
include "mulcld.mm"
include "recld.mm"
include "remulcld.mm"
include "abscl.mm"
include "syl.mm"
include "resqcld.mm"
include "readdcld.mm"
include "releabs.mm"
include "wceq.mm"
include "absmul.mm"
include "syl2anc.mm"
include "abscj.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "crp.mm"
include "2rp.mm"
include "lemul2d.mm"
include "mpbid.mm"
include "leadd2dd.mm"
include "sqabsadd.mm"
include "recnd.mm"
include "binom2.mm"
include "add32d.mm"
include "3brtr4d.mm"
include "addcl.mm"
include "cc0.mm"
include "absge0.mm"
include "addge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"

theorem abstri
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( abs ` ( A + B ) ) <_ ( ( abs ` A ) + ( abs ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cabs
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    @4
    c2
    cexp
    co
    #
    @7
    c2
    cexp
    co
    #
    cle
    wbr
    @2
    @5
    c2
    cexp
    co
    #
    @6
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    cA
    cB
    ccj
    cfv
    #
    cmul
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @12
    c2
    @5
    @6
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    @9
    cle
    @2
    @16
    @18
    @12
    @2
    c2
    @15
    c2
    cr
    wcel
    @2
    2re
    a1i
    #
    @2
    @14
    @2
    cA
    @13
    @0
    @1
    simpl
    #
    @2
    cB
    @0
    @1
    simpr
    #
    cjcld
    #
    mulcld
    #
    recld
    #
    remulcld
    @2
    c2
    @17
    @20
    @2
    @5
    @6
    @2
    @0
    @5
    cr
    wcel
    @21
    cA
    abscl
    syl
    #
    @2
    @1
    @6
    cr
    wcel
    @22
    cB
    abscl
    syl
    #
    remulcld
    #
    remulcld
    #
    @2
    @10
    @11
    @2
    @5
    @26
    resqcld
    #
    @2
    @6
    @27
    resqcld
    #
    readdcld
    @2
    @15
    @17
    cle
    wbr
    @16
    @18
    cle
    wbr
    @2
    @15
    @14
    cabs
    cfv
    #
    @17
    cle
    @2
    @14
    cc
    wcel
    @15
    @32
    cle
    wbr
    @24
    @14
    releabs
    syl
    @2
    @32
    @5
    @13
    cabs
    cfv
    #
    cmul
    co
    #
    @17
    @2
    @0
    @13
    cc
    wcel
    @32
    @34
    wceq
    @21
    @23
    cA
    @13
    absmul
    syl2anc
    @2
    @33
    @6
    @5
    cmul
    @2
    @1
    @33
    @6
    wceq
    @22
    cB
    abscj
    syl
    oveq2d
    eqtrd
    breqtrd
    @2
    @15
    @17
    c2
    @25
    @28
    c2
    crp
    wcel
    @2
    2rp
    a1i
    lemul2d
    mpbid
    leadd2dd
    cA
    cB
    sqabsadd
    @2
    @9
    @10
    @18
    caddc
    co
    @11
    caddc
    co
    #
    @19
    @2
    @5
    cc
    wcel
    @6
    cc
    wcel
    @9
    @35
    wceq
    @2
    @5
    @26
    recnd
    @2
    @6
    @27
    recnd
    @5
    @6
    binom2
    syl2anc
    @2
    @10
    @18
    @11
    @2
    @10
    @30
    recnd
    @2
    @18
    @29
    recnd
    @2
    @11
    @31
    recnd
    add32d
    eqtrd
    3brtr4d
    @2
    @4
    @7
    @2
    @3
    cc
    wcel
    #
    @4
    cr
    wcel
    cA
    cB
    addcl
    #
    @3
    abscl
    syl
    @2
    @5
    @6
    @26
    @27
    readdcld
    @2
    @36
    cc0
    @4
    cle
    wbr
    @37
    @3
    absge0
    syl
    @2
    @5
    @6
    @26
    @27
    @2
    @0
    cc0
    @5
    cle
    wbr
    @21
    cA
    absge0
    syl
    @2
    @1
    cc0
    @6
    cle
    wbr
    @22
    cB
    absge0
    syl
    addge0d
    le2sqd
    mpbird
end
