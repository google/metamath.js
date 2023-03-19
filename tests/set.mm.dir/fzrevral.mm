include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "cv.mm"
include "cmin.mm"
include "wsbc.mm"
include "wi.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "elfzelz.mm"
include "fzrev.mm"
include "anassrs.mm"
include "sylan2.mm"
include "mpbid.mm"
include "rspsbc.mm"
include "syl.mm"
include "ex.mm"
include "3impa.mm"
include "com23.mm"
include "ralrimdv.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfral.mm"
include "fzrev2i.mm"
include "wceq.mm"
include "oveq2.mm"
include "sbceq1d.mm"
include "rspcv.mm"
include "cc.mm"
include "zcn.mm"
include "zcnd.mm"
include "nncan.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "sbceq1a.mm"
include "sylibrd.mm"
include "ralrimd.mm"
include "3ad2ant3.mm"
include "impbid.mm"

theorem fzrevral
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x

  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint k ph
  disjoint j x
  disjoint k x
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) -> ( A. j e. ( M ... N ) ph <-> A. k e. ( ( K - N ) ... ( K - M ) ) [. ( K - k ) / j ]. ph ) )

  proof
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
    w3a
    #
    wph
    vj
    cM
    cN
    cfz
    co
    #
    wral
    #
    wph
    vj
    cK
    vk
    cv
    #
    cmin
    co
    #
    wsbc
    #
    vk
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
    wral
    #
    @3
    @5
    @8
    vk
    @11
    @3
    @6
    @11
    wcel
    #
    @5
    @8
    @0
    @1
    @2
    @13
    @5
    @8
    wi
    #
    wi
    @0
    @1
    wa
    #
    @2
    wa
    #
    @13
    @14
    @16
    @13
    wa
    #
    @7
    @4
    wcel
    #
    @14
    @17
    @13
    @18
    @16
    @13
    simpr
    @13
    @16
    @6
    cz
    wcel
    #
    @13
    @18
    wb
    #
    @6
    @9
    @10
    elfzelz
    @15
    @2
    @19
    @20
    cK
    @6
    cM
    cN
    fzrev
    anassrs
    sylan2
    mpbid
    wph
    vj
    @7
    @4
    rspsbc
    syl
    ex
    3impa
    com23
    ralrimdv
    @2
    @0
    @12
    @5
    wi
    @1
    @2
    @12
    wph
    vj
    @4
    @2
    vj
    nfv
    @8
    vj
    vk
    @11
    vj
    @11
    nfcv
    wph
    vj
    @7
    nfsbc1v
    nfral
    @2
    vj
    cv
    #
    @4
    wcel
    #
    @12
    wph
    @2
    @22
    @12
    wph
    wi
    @2
    @22
    wa
    #
    @12
    wph
    vj
    cK
    cK
    @21
    cmin
    co
    #
    cmin
    co
    #
    wsbc
    #
    wph
    @23
    @24
    @11
    wcel
    @12
    @26
    wi
    cK
    @21
    cM
    cN
    fzrev2i
    @8
    @26
    vk
    @24
    @11
    @6
    @24
    wceq
    wph
    vj
    @7
    @25
    @6
    @24
    cK
    cmin
    oveq2
    sbceq1d
    rspcv
    syl
    @23
    @21
    @25
    wceq
    wph
    @26
    wb
    @23
    @25
    @21
    @2
    cK
    cc
    wcel
    @21
    cc
    wcel
    @25
    @21
    wceq
    @22
    cK
    zcn
    @22
    @21
    @21
    cM
    cN
    elfzelz
    zcnd
    cK
    @21
    nncan
    syl2an
    eqcomd
    wph
    vj
    @25
    sbceq1a
    syl
    sylibrd
    ex
    com23
    ralrimd
    3ad2ant3
    impbid
end
