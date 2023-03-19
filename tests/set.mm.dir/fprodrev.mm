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
include "ad2antrl.mm"
include "fzrev.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "ad2antll.mm"
include "cc.mm"
include "zcnd.mm"
include "nncand.mm"
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
include "fvmpt.mm"
include "adantl.mm"
include "fprodf1o.mm"

theorem fprodrev
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  assume fprodshft.1: |- ( ph -> K e. ZZ )
  assume fprodshft.2: |- ( ph -> M e. ZZ )
  assume fprodshft.3: |- ( ph -> N e. ZZ )
  assume fprodshft.4: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fprodrev.5: |- ( j = ( K - k ) -> A = B )

  disjoint A k
  disjoint B j
  disjoint j k
  disjoint j ph
  disjoint K j
  disjoint K k
  disjoint k ph
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  assert |- ( ph -> prod_ j e. ( M ... N ) A = prod_ k e. ( ( K - N ) ... ( K - M ) ) B )

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
    fprodrev.5
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
    @22
    wb
    wph
    @23
    @17
    fprodshft.2
    adantr
    wph
    @24
    @17
    fprodshft.3
    adantr
    wph
    @25
    @17
    fprodshft.1
    adantr
    @15
    @26
    wph
    @16
    @4
    @1
    @2
    elfzelz
    #
    ad2antrl
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
    @16
    @8
    @28
    wceq
    wph
    @15
    @7
    @5
    cK
    cmin
    oveq2
    ad2antll
    @21
    cK
    @4
    wph
    cK
    cc
    wcel
    #
    @17
    wph
    cK
    fprodshft.1
    zcnd
    #
    adantr
    @15
    @4
    cc
    wcel
    wph
    @16
    @15
    @4
    @27
    zcnd
    ad2antrl
    nncand
    eqtr2d
    jca
    wph
    @20
    wa
    #
    @15
    @16
    @31
    @4
    @8
    @3
    wph
    @18
    @19
    simprr
    @31
    @18
    @8
    @3
    wcel
    #
    wph
    @18
    @19
    simprl
    @31
    @23
    @24
    @25
    @7
    cz
    wcel
    #
    @18
    @32
    wb
    wph
    @23
    @20
    fprodshft.2
    adantr
    wph
    @24
    @20
    fprodshft.3
    adantr
    wph
    @25
    @20
    fprodshft.1
    adantr
    @18
    @33
    wph
    @19
    @7
    cM
    cN
    elfzelz
    #
    ad2antrl
    cK
    @7
    cM
    cN
    fzrev2
    syl22anc
    mpbid
    eqeltrd
    @31
    @5
    cK
    @8
    cmin
    co
    #
    @7
    @19
    @5
    @35
    wceq
    wph
    @18
    @4
    @8
    cK
    cmin
    oveq2
    ad2antll
    @31
    cK
    @7
    wph
    @29
    @20
    @30
    adantr
    @18
    @7
    cc
    wcel
    wph
    @19
    @18
    @7
    @34
    zcnd
    ad2antrl
    nncand
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
    fprodshft.4
    fprodf1o
end
