include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "oveq1.mm"
include "0csh0.mm"
include "a1i.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "a1d.mm"
include "wne.mm"
include "cmo.mm"
include "cop.mm"
include "csubstr.mm"
include "cc0.mm"
include "cconcat.mm"
include "caddc.mm"
include "cshword.mm"
include "adantr.mm"
include "swrdcl.mm"
include "ccatlen.mm"
include "syl2anc.mm"
include "cn.mm"
include "lennncl.mm"
include "pm3.21.mm"
include "ex.mm"
include "syl.mm"
include "com24.mm"
include "pm2.43i.mm"
include "imp31.mm"
include "cmin.mm"
include "cfz.mm"
include "simpl.mm"
include "pm3.22.mm"
include "adantl.mm"
include "zmodfzp1.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "zmodcl.mm"
include "ancoms.mm"
include "0elfz.mm"
include "oveq12d.mm"
include "cc.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "oveq2d.mm"
include "npcan.mm"
include "syl2an.mm"
include "expcom.mm"
include "pm2.61ine.mm"

theorem cshwlen
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( # ` ( W cyclShift N ) ) = ( # ` W ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    wceq
    #
    wi
    cW
    c0
    cW
    c0
    wceq
    #
    @7
    @3
    @8
    @4
    cW
    chash
    @8
    @4
    c0
    cN
    ccsh
    co
    #
    c0
    cW
    cW
    c0
    cN
    ccsh
    oveq1
    @9
    c0
    wceq
    @8
    cN
    0csh0
    a1i
    @8
    c0
    cW
    wceq
    cW
    c0
    eqcom
    biimpi
    3eqtrd
    fveq2d
    a1d
    @3
    cW
    c0
    wne
    #
    @7
    @3
    @10
    wa
    #
    @5
    cW
    cN
    @6
    cmo
    co
    #
    @6
    cop
    csubstr
    co
    #
    cW
    cc0
    @12
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    chash
    cfv
    #
    @13
    chash
    cfv
    #
    @14
    chash
    cfv
    #
    caddc
    co
    #
    @6
    @3
    @5
    @16
    wceq
    @10
    @3
    @4
    @15
    chash
    cN
    cV
    cW
    cshword
    fveq2d
    adantr
    @3
    @16
    @19
    wceq
    #
    @10
    @1
    @20
    @2
    @1
    @13
    @0
    wcel
    @14
    @0
    wcel
    @20
    cV
    cW
    @12
    @6
    swrdcl
    cV
    cW
    cc0
    @12
    swrdcl
    cV
    @13
    @14
    ccatlen
    syl2anc
    adantr
    adantr
    @11
    @1
    @6
    cn
    wcel
    #
    @2
    wa
    #
    wa
    #
    @19
    @6
    wceq
    @1
    @2
    @10
    @23
    @1
    @2
    @10
    @23
    wi
    wi
    @1
    @10
    @2
    @1
    @23
    @1
    @10
    @2
    @1
    @23
    wi
    #
    wi
    #
    @1
    @10
    wa
    @21
    @25
    cV
    cW
    lennncl
    @21
    @2
    @24
    @22
    @1
    pm3.21
    ex
    syl
    ex
    com24
    pm2.43i
    imp31
    @23
    @19
    @6
    @12
    cmin
    co
    #
    @12
    cc0
    cmin
    co
    #
    caddc
    co
    @26
    @12
    caddc
    co
    #
    @6
    @23
    @17
    @26
    @18
    @27
    caddc
    @23
    @1
    @12
    cc0
    @6
    cfz
    co
    #
    wcel
    #
    @6
    @29
    wcel
    #
    @17
    @26
    wceq
    @1
    @22
    simpl
    #
    @23
    @2
    @21
    wa
    #
    @30
    @22
    @33
    @1
    @21
    @2
    pm3.22
    adantl
    cN
    @6
    zmodfzp1
    syl
    #
    @1
    @31
    @22
    @1
    @6
    cn0
    wcel
    @31
    cV
    cW
    lencl
    #
    @6
    nn0fz0
    sylib
    adantr
    cV
    cW
    @12
    @6
    swrdlen
    syl3anc
    @23
    @1
    cc0
    cc0
    @12
    cfz
    co
    wcel
    #
    @30
    @18
    @27
    wceq
    @32
    @23
    @12
    cn0
    wcel
    #
    @36
    @22
    @37
    @1
    @2
    @21
    @37
    cN
    @6
    zmodcl
    #
    ancoms
    adantl
    @12
    0elfz
    syl
    @34
    cV
    cW
    cc0
    @12
    swrdlen
    syl3anc
    oveq12d
    @23
    @27
    @12
    @26
    caddc
    @23
    @12
    @22
    @12
    cc
    wcel
    #
    @1
    @2
    @21
    @39
    @33
    @12
    @38
    nn0cnd
    ancoms
    #
    adantl
    subid1d
    oveq2d
    @1
    @6
    cc
    wcel
    @39
    @28
    @6
    wceq
    @22
    @1
    @6
    @35
    nn0cnd
    @40
    @6
    @12
    npcan
    syl2an
    3eqtrd
    syl
    3eqtrd
    expcom
    pm2.61ine
end
