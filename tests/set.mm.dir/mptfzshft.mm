include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "a1i.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simprr.mm"
include "oveq1d.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "cc.mm"
include "zcn.mm"
include "npcan.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "simprl.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "zsubcld.mm"
include "eqeltrd.mm"
include "fzaddel.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "jca.mm"
include "mpbid.mm"
include "pncan.mm"
include "impbida.mm"
include "mptcnv.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem mptfzshft
  let wph: wff ph
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  assume mptfzshft.1: |- ( ph -> K e. ZZ )
  assume mptfzshft.2: |- ( ph -> M e. ZZ )
  assume mptfzshft.3: |- ( ph -> N e. ZZ )

  disjoint K j
  disjoint M j
  disjoint N j
  disjoint j ph
  disjoint j k
  disjoint K k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( j e. ( ( M + K ) ... ( N + K ) ) |-> ( j - K ) ) : ( ( M + K ) ... ( N + K ) ) -1-1-onto-> ( M ... N ) )

  proof
    wph
    vj
    cM
    cK
    caddc
    co
    #
    cN
    cK
    caddc
    co
    #
    cfz
    co
    #
    vj
    cv
    #
    cK
    cmin
    co
    #
    cmpt
    #
    @2
    wfn
    #
    @5
    ccnv
    #
    cM
    cN
    cfz
    co
    #
    wfn
    #
    @2
    @8
    @5
    wf1o
    @6
    wph
    vj
    @2
    @4
    @5
    @3
    cK
    cmin
    ovex
    @5
    eqid
    fnmpti
    a1i
    wph
    @9
    vk
    @8
    vk
    cv
    #
    cK
    caddc
    co
    #
    cmpt
    #
    @8
    wfn
    vk
    @8
    @11
    @12
    @10
    cK
    caddc
    ovex
    @12
    eqid
    fnmpti
    wph
    @8
    @7
    @12
    wph
    vj
    vk
    @2
    @4
    @8
    @11
    wph
    @3
    @2
    wcel
    #
    @10
    @4
    wceq
    #
    wa
    #
    @10
    @8
    wcel
    #
    @3
    @11
    wceq
    #
    wa
    #
    wph
    @15
    wa
    #
    @16
    @17
    @19
    @16
    @11
    @2
    wcel
    #
    @19
    @3
    @11
    @2
    @19
    @11
    @4
    cK
    caddc
    co
    #
    @3
    @19
    @10
    @4
    cK
    caddc
    wph
    @13
    @14
    simprr
    #
    oveq1d
    @19
    @3
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @21
    @3
    wceq
    #
    @13
    @23
    wph
    @14
    @3
    @0
    @1
    elfzelz
    ad2antrl
    #
    wph
    @24
    @15
    mptfzshft.1
    adantr
    #
    @23
    @3
    cc
    wcel
    cK
    cc
    wcel
    #
    @25
    @24
    @3
    zcn
    cK
    zcn
    #
    @3
    cK
    npcan
    syl2an
    syl2anc
    eqtr2d
    #
    wph
    @13
    @14
    simprl
    eqeltrrd
    @19
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    @24
    @16
    @20
    wb
    #
    wph
    @31
    @15
    mptfzshft.2
    adantr
    wph
    @32
    @15
    mptfzshft.3
    adantr
    @19
    @10
    @4
    cz
    @22
    @19
    @3
    cK
    @26
    @27
    zsubcld
    eqeltrd
    @27
    @10
    cK
    cM
    cN
    fzaddel
    #
    syl22anc
    mpbird
    @30
    jca
    wph
    @18
    wa
    #
    @13
    @14
    @36
    @3
    @11
    @2
    wph
    @16
    @17
    simprr
    #
    @36
    @16
    @20
    wph
    @16
    @17
    simprl
    @36
    @31
    @32
    @33
    @24
    @34
    wph
    @31
    @18
    mptfzshft.2
    adantr
    wph
    @32
    @18
    mptfzshft.3
    adantr
    @16
    @33
    wph
    @17
    @10
    cM
    cN
    elfzelz
    ad2antrl
    #
    wph
    @24
    @18
    mptfzshft.1
    adantr
    #
    @35
    syl22anc
    mpbid
    eqeltrd
    @36
    @4
    @11
    cK
    cmin
    co
    #
    @10
    @36
    @3
    @11
    cK
    cmin
    @37
    oveq1d
    @36
    @33
    @24
    @40
    @10
    wceq
    #
    @38
    @39
    @33
    @10
    cc
    wcel
    @28
    @41
    @24
    @10
    zcn
    @29
    @10
    cK
    pncan
    syl2an
    syl2anc
    eqtr2d
    jca
    impbida
    mptcnv
    fneq1d
    mpbiri
    @2
    @8
    @5
    dff1o4
    sylanbrc
end
