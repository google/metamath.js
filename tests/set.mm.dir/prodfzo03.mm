include "cc0.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "cprod.mm"
include "csn.mm"
include "c1.mm"
include "cmul.mm"
include "c2.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "fzodisjsn.mm"
include "a1i.mm"
include "cun.mm"
include "caddc.mm"
include "2p1e3.mm"
include "oveq2i.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "2eluzge0.mm"
include "fzosplitsn.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "cfn.mm"
include "fzofi.mm"
include "fprodsplit.mm"
include "wne.mm"
include "0ne1.mm"
include "disjsn2.mm"
include "mp1i.mm"
include "cpr.mm"
include "fzo0to2pr.mm"
include "df-pr.mm"
include "eqtri.mm"
include "cv.mm"
include "cc.mm"
include "wss.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "2z.mm"
include "3z.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "fzoss2.mm"
include "sseli.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "snfi.mm"
include "velsn.mm"
include "wa.mm"
include "adantl.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wrex.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "eqid.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "r19.29a.mm"
include "eqeltrd.mm"
include "sylan2b.mm"
include "fprodcl.mm"
include "1ex.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "mulassd.mm"
include "cn0.mm"
include "0nn0.mm"
include "prodsn.mm"
include "syl2anc.mm"
include "1nn0.mm"
include "2nn0.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem prodfzo03
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume prodfzo03.1: |- ( k = 0 -> D = A )
  assume prodfzo03.2: |- ( k = 1 -> D = B )
  assume prodfzo03.3: |- ( k = 2 -> D = C )
  assume prodfzo03.a: |- ( ( ph /\ k e. ( 0 ..^ 3 ) ) -> D e. CC )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> prod_ k e. ( 0 ..^ 3 ) D = ( A x. ( B x. C ) ) )

  proof
    wph
    cc0
    c3
    cfzo
    co
    #
    cD
    vk
    cprod
    #
    cc0
    csn
    #
    cD
    vk
    cprod
    #
    c1
    csn
    #
    cD
    vk
    cprod
    #
    cmul
    co
    #
    c2
    csn
    #
    cD
    vk
    cprod
    #
    cmul
    co
    #
    @3
    @5
    @8
    cmul
    co
    #
    cmul
    co
    cA
    cB
    cC
    cmul
    co
    #
    cmul
    co
    wph
    @1
    cc0
    c2
    cfzo
    co
    #
    cD
    vk
    cprod
    #
    @8
    cmul
    co
    @9
    wph
    @12
    @7
    cD
    @0
    vk
    @12
    @7
    cin
    c0
    wceq
    wph
    cc0
    c2
    fzodisjsn
    a1i
    @0
    @12
    @7
    cun
    #
    wceq
    wph
    cc0
    c2
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @0
    @14
    @15
    c3
    cc0
    cfzo
    2p1e3
    oveq2i
    c2
    cc0
    cuz
    cfv
    wcel
    @16
    @14
    wceq
    2eluzge0
    cc0
    c2
    fzosplitsn
    ax-mp
    eqtr3i
    a1i
    @0
    cfn
    wcel
    wph
    cc0
    c3
    fzofi
    a1i
    prodfzo03.a
    fprodsplit
    wph
    @13
    @6
    @8
    cmul
    wph
    @2
    @4
    cD
    @12
    vk
    cc0
    c1
    wne
    @2
    @4
    cin
    c0
    wceq
    wph
    0ne1
    cc0
    c1
    disjsn2
    mp1i
    @12
    @2
    @4
    cun
    #
    wceq
    wph
    @12
    cc0
    c1
    cpr
    @17
    fzo0to2pr
    cc0
    c1
    df-pr
    eqtri
    a1i
    @12
    cfn
    wcel
    wph
    cc0
    c2
    fzofi
    a1i
    vk
    cv
    #
    @12
    wcel
    wph
    @18
    @0
    wcel
    #
    cD
    cc
    wcel
    #
    @12
    @0
    @18
    c3
    c2
    cuz
    cfv
    wcel
    #
    @12
    @0
    wss
    @21
    c2
    cz
    wcel
    c3
    cz
    wcel
    c2
    c3
    cle
    wbr
    2z
    3z
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    c2
    c3
    eluz2
    mpbir3an
    c2
    cc0
    c3
    fzoss2
    ax-mp
    sseli
    prodfzo03.a
    sylan2
    fprodsplit
    oveq1d
    eqtrd
    wph
    @3
    @5
    @8
    wph
    @2
    cD
    vk
    @2
    cfn
    wcel
    wph
    cc0
    snfi
    a1i
    @18
    @2
    wcel
    wph
    @18
    cc0
    wceq
    #
    @20
    vk
    cc0
    velsn
    wph
    @22
    wa
    cD
    cA
    cc
    @22
    cD
    cA
    wceq
    #
    wph
    prodfzo03.1
    adantl
    wph
    cA
    cc
    wcel
    #
    @22
    wph
    @23
    @24
    vk
    @0
    wph
    @19
    wa
    #
    @23
    wa
    cD
    cA
    cc
    @25
    @23
    simpr
    @25
    @20
    @23
    prodfzo03.a
    adantr
    eqeltrrd
    @23
    vk
    @0
    wrex
    #
    wph
    cc0
    @0
    wcel
    cA
    cA
    wceq
    #
    @26
    cc0
    cc0
    c1
    c2
    ctp
    #
    @0
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    cA
    eqid
    @23
    @27
    vk
    cc0
    @0
    @22
    cD
    cA
    cA
    prodfzo03.1
    eqeq1d
    rspcev
    mp2an
    a1i
    r19.29a
    #
    adantr
    eqeltrd
    sylan2b
    fprodcl
    wph
    @4
    cD
    vk
    @4
    cfn
    wcel
    wph
    c1
    snfi
    a1i
    @18
    @4
    wcel
    wph
    @18
    c1
    wceq
    #
    @20
    vk
    c1
    velsn
    wph
    @30
    wa
    cD
    cB
    cc
    @30
    cD
    cB
    wceq
    #
    wph
    prodfzo03.2
    adantl
    wph
    cB
    cc
    wcel
    #
    @30
    wph
    @31
    @32
    vk
    @0
    @25
    @31
    wa
    cD
    cB
    cc
    @25
    @31
    simpr
    @25
    @20
    @31
    prodfzo03.a
    adantr
    eqeltrrd
    @31
    vk
    @0
    wrex
    #
    wph
    c1
    @0
    wcel
    cB
    cB
    wceq
    #
    @33
    c1
    @28
    @0
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    cB
    eqid
    @31
    @34
    vk
    c1
    @0
    @30
    cD
    cB
    cB
    prodfzo03.2
    eqeq1d
    rspcev
    mp2an
    a1i
    r19.29a
    #
    adantr
    eqeltrd
    sylan2b
    fprodcl
    wph
    @7
    cD
    vk
    @7
    cfn
    wcel
    wph
    c2
    snfi
    a1i
    @18
    @7
    wcel
    wph
    @18
    c2
    wceq
    #
    @20
    vk
    c2
    velsn
    wph
    @36
    wa
    cD
    cC
    cc
    @36
    cD
    cC
    wceq
    #
    wph
    prodfzo03.3
    adantl
    wph
    cC
    cc
    wcel
    #
    @36
    wph
    @37
    @38
    vk
    @0
    @25
    @37
    wa
    cD
    cC
    cc
    @25
    @37
    simpr
    @25
    @20
    @37
    prodfzo03.a
    adantr
    eqeltrrd
    @37
    vk
    @0
    wrex
    #
    wph
    c2
    @0
    wcel
    cC
    cC
    wceq
    #
    @39
    c2
    @28
    @0
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    cC
    eqid
    @37
    @40
    vk
    c2
    @0
    @36
    cD
    cC
    cC
    prodfzo03.3
    eqeq1d
    rspcev
    mp2an
    a1i
    r19.29a
    #
    adantr
    eqeltrd
    sylan2b
    fprodcl
    mulassd
    wph
    @3
    cA
    @10
    @11
    cmul
    wph
    cc0
    cn0
    wcel
    #
    @24
    @3
    cA
    wceq
    @42
    wph
    0nn0
    a1i
    @29
    cD
    cA
    vk
    cc0
    cn0
    prodfzo03.1
    prodsn
    syl2anc
    wph
    @5
    cB
    @8
    cC
    cmul
    wph
    c1
    cn0
    wcel
    #
    @32
    @5
    cB
    wceq
    @43
    wph
    1nn0
    a1i
    @35
    cD
    cB
    vk
    c1
    cn0
    prodfzo03.2
    prodsn
    syl2anc
    wph
    c2
    cn0
    wcel
    #
    @38
    @8
    cC
    wceq
    @44
    wph
    2nn0
    a1i
    @41
    cD
    cC
    vk
    c2
    cn0
    prodfzo03.3
    prodsn
    syl2anc
    oveq12d
    oveq12d
    3eqtrd
end
