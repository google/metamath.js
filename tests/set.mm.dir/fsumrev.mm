include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "fzfid.mm"
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
include "simprl.mm"
include "cz.mm"
include "wb.mm"
include "adantr.mm"
include "elfzelz.mm"
include "syl.mm"
include "fzrev.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "oveq2d.mm"
include "cc.mm"
include "zcn.mm"
include "nncan.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "jca.mm"
include "fzrev2.mm"
include "impbida.mm"
include "mptcnv.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "dff1o4.mm"
include "sylanbrc.mm"
include "cfv.mm"
include "oveq2.mm"
include "fvmpt.mm"
include "adantl.mm"
include "fsumf1o.mm"

theorem fsumrev
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume fsumrev.1: |- ( ph -> K e. ZZ )
  assume fsumrev.2: |- ( ph -> M e. ZZ )
  assume fsumrev.3: |- ( ph -> N e. ZZ )
  assume fsumrev.4: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fsumrev.5: |- ( j = ( K - k ) -> A = B )

  disjoint A k
  disjoint B j
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  disjoint k m
  disjoint A m
  disjoint j m
  disjoint K m
  disjoint M m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> sum_ j e. ( M ... N ) A = sum_ k e. ( ( K - N ) ... ( K - M ) ) B )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cA
    cK
    cN
    cmin
    co
    #
    cK
    cM
    cmin
    co
    #
    cfz
    co
    #
    cB
    vj
    vk
    vj
    @3
    cK
    vj
    cv
    #
    cmin
    co
    #
    cmpt
    #
    cK
    vk
    cv
    #
    cmin
    co
    #
    fsumrev.5
    wph
    @1
    @2
    fzfid
    wph
    @6
    @3
    wfn
    #
    @6
    ccnv
    #
    @0
    wfn
    #
    @3
    @0
    @6
    wf1o
    @9
    wph
    vj
    @3
    @5
    @6
    cK
    @4
    cmin
    ovex
    @6
    eqid
    #
    fnmpti
    a1i
    wph
    @11
    vk
    @0
    @8
    cmpt
    #
    @0
    wfn
    vk
    @0
    @8
    @13
    cK
    @7
    cmin
    ovex
    #
    @13
    eqid
    fnmpti
    wph
    @0
    @10
    @13
    wph
    vj
    vk
    @3
    @5
    @0
    @8
    wph
    @4
    @3
    wcel
    #
    @7
    @5
    wceq
    #
    wa
    #
    @7
    @0
    wcel
    #
    @4
    @8
    wceq
    #
    wa
    #
    wph
    @17
    wa
    #
    @18
    @19
    @21
    @7
    @5
    @0
    wph
    @15
    @16
    simprr
    #
    @21
    @15
    @5
    @0
    wcel
    #
    wph
    @15
    @16
    simprl
    #
    @21
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @15
    @23
    wb
    wph
    @25
    @17
    fsumrev.2
    adantr
    wph
    @26
    @17
    fsumrev.3
    adantr
    wph
    @27
    @17
    fsumrev.1
    adantr
    #
    @21
    @15
    @28
    @24
    @4
    @1
    @2
    elfzelz
    syl
    #
    cK
    @4
    cM
    cN
    fzrev
    syl22anc
    mpbid
    eqeltrd
    @21
    @8
    cK
    @5
    cmin
    co
    #
    @4
    @21
    @7
    @5
    cK
    cmin
    @22
    oveq2d
    @21
    @27
    @28
    @31
    @4
    wceq
    #
    @29
    @30
    @27
    cK
    cc
    wcel
    #
    @4
    cc
    wcel
    @32
    @28
    cK
    zcn
    #
    @4
    zcn
    cK
    @4
    nncan
    syl2an
    syl2anc
    eqtr2d
    jca
    wph
    @20
    wa
    #
    @15
    @16
    @35
    @4
    @8
    @3
    wph
    @18
    @19
    simprr
    #
    @35
    @18
    @8
    @3
    wcel
    #
    wph
    @18
    @19
    simprl
    #
    @35
    @25
    @26
    @27
    @7
    cz
    wcel
    #
    @18
    @37
    wb
    wph
    @25
    @20
    fsumrev.2
    adantr
    wph
    @26
    @20
    fsumrev.3
    adantr
    wph
    @27
    @20
    fsumrev.1
    adantr
    #
    @35
    @18
    @39
    @38
    @7
    cM
    cN
    elfzelz
    syl
    #
    cK
    @7
    cM
    cN
    fzrev2
    syl22anc
    mpbid
    eqeltrd
    @35
    @5
    cK
    @8
    cmin
    co
    #
    @7
    @35
    @4
    @8
    cK
    cmin
    @36
    oveq2d
    @35
    @27
    @39
    @42
    @7
    wceq
    #
    @40
    @41
    @27
    @33
    @7
    cc
    wcel
    @43
    @39
    @34
    @7
    zcn
    cK
    @7
    nncan
    syl2an
    syl2anc
    eqtr2d
    jca
    impbida
    mptcnv
    fneq1d
    mpbiri
    @3
    @0
    @6
    dff1o4
    sylanbrc
    @7
    @3
    wcel
    @7
    @6
    cfv
    @8
    wceq
    wph
    vj
    @7
    @5
    @8
    @3
    @6
    @4
    @7
    cK
    cmin
    oveq2
    @12
    @14
    fvmpt
    adantl
    fsumrev.4
    fsumf1o
end
