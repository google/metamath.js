include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "w3a.mm"
include "simpr.mm"
include "adantr.mm"
include "zsubcl.mm"
include "ancoms.mm"
include "adantl.mm"
include "3jca.mm"
include "3cshw.mm"
include "syl.mm"
include "simpl.mm"
include "ancomd.mm"
include "eqcomd.mm"
include "cshwleneq.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "2cshw.mm"
include "cc.mm"
include "zcn.mm"
include "anim12i.mm"
include "pncan3.mm"
include "3eqtrd.mm"
include "lencl.mm"
include "nn0zd.mm"
include "syl2an.mm"
include "nn0cnd.mm"
include "cshwn.mm"
include "ex.mm"

theorem cshweqdif2
  let cU: class U
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( ( W e. Word V /\ U e. Word V ) /\ ( N e. ZZ /\ M e. ZZ ) ) -> ( ( W cyclShift N ) = ( U cyclShift M ) -> ( U cyclShift ( M - N ) ) = W ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    wa
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    cU
    cM
    ccsh
    co
    #
    wceq
    #
    cU
    cM
    cN
    cmin
    co
    #
    ccsh
    co
    #
    cW
    wceq
    @7
    @10
    wa
    #
    @12
    cW
    cM
    cW
    chash
    cfv
    #
    cM
    cmin
    co
    #
    caddc
    co
    #
    ccsh
    co
    #
    cW
    @14
    ccsh
    co
    #
    cW
    @13
    @12
    @9
    @11
    ccsh
    co
    #
    @15
    ccsh
    co
    #
    cW
    cM
    ccsh
    co
    #
    @15
    ccsh
    co
    #
    @17
    @13
    @12
    @19
    cU
    chash
    cfv
    #
    cM
    cmin
    co
    #
    ccsh
    co
    #
    @20
    @13
    @2
    @11
    cz
    wcel
    #
    @5
    w3a
    #
    @12
    @25
    wceq
    @7
    @27
    @10
    @7
    @2
    @26
    @5
    @3
    @2
    @6
    @1
    @2
    simpr
    adantr
    @6
    @26
    @3
    @5
    @4
    @26
    cM
    cN
    zsubcl
    ancoms
    adantl
    #
    @6
    @5
    @3
    @4
    @5
    simpr
    #
    adantl
    #
    3jca
    adantr
    cM
    @11
    cV
    cU
    3cshw
    syl
    @13
    @24
    @15
    @19
    ccsh
    @13
    @23
    @14
    cM
    cmin
    @13
    @2
    @1
    wa
    #
    @5
    @4
    wa
    #
    @9
    @8
    wceq
    @23
    @14
    wceq
    @7
    @31
    @10
    @7
    @1
    @2
    @3
    @6
    simpl
    ancomd
    adantr
    @7
    @32
    @10
    @7
    @4
    @5
    @3
    @6
    simpr
    ancomd
    adantr
    @13
    @8
    @9
    @7
    @10
    simpr
    eqcomd
    #
    cW
    cN
    cM
    cV
    cU
    cshwleneq
    syl3anc
    oveq1d
    oveq2d
    eqtrd
    @13
    @19
    @21
    @15
    ccsh
    @13
    @19
    @8
    @11
    ccsh
    co
    #
    cW
    cN
    @11
    caddc
    co
    #
    ccsh
    co
    #
    @21
    @13
    @9
    @8
    @11
    ccsh
    @33
    oveq1d
    @13
    @1
    @4
    @26
    w3a
    #
    @34
    @36
    wceq
    @7
    @37
    @10
    @7
    @1
    @4
    @26
    @3
    @1
    @6
    @1
    @2
    simpl
    adantr
    #
    @6
    @4
    @3
    @4
    @5
    simpl
    adantl
    @28
    3jca
    adantr
    cN
    @11
    cV
    cW
    2cshw
    syl
    @13
    @35
    cM
    cW
    ccsh
    @13
    cN
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    wa
    #
    @35
    cM
    wceq
    @7
    @41
    @10
    @6
    @41
    @3
    @4
    @39
    @5
    @40
    cN
    zcn
    cM
    zcn
    #
    anim12i
    adantl
    adantr
    cN
    cM
    pncan3
    syl
    oveq2d
    3eqtrd
    oveq1d
    @13
    @1
    @5
    @15
    cz
    wcel
    #
    w3a
    #
    @22
    @17
    wceq
    @7
    @44
    @10
    @7
    @1
    @5
    @43
    @38
    @30
    @3
    @14
    cz
    wcel
    #
    @5
    @43
    @6
    @1
    @45
    @2
    @1
    @14
    cV
    cW
    lencl
    #
    nn0zd
    adantr
    @29
    @14
    cM
    zsubcl
    syl2an
    3jca
    adantr
    cM
    @15
    cV
    cW
    2cshw
    syl
    3eqtrd
    @13
    @16
    @14
    cW
    ccsh
    @13
    @40
    @14
    cc
    wcel
    #
    wa
    #
    @16
    @14
    wceq
    @7
    @48
    @10
    @7
    @47
    @40
    @3
    @47
    @6
    @40
    @1
    @47
    @2
    @1
    @14
    @46
    nn0cnd
    adantr
    @5
    @40
    @4
    @42
    adantl
    anim12i
    ancomd
    adantr
    cM
    @14
    pncan3
    syl
    oveq2d
    @7
    @18
    cW
    wceq
    #
    @10
    @7
    @1
    @49
    @38
    cV
    cW
    cshwn
    syl
    adantr
    3eqtrd
    ex
end
