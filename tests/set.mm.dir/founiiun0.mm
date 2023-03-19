include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wfo.mm"
include "cuni.mm"
include "cv.mm"
include "ciun.mm"
include "cfv.mm"
include "wceq.mm"
include "uniiun.mm"
include "a1i.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "elun1.mm"
include "adantl.mm"
include "foelrni.mm"
include "syl2anc.mm"
include "eqimss2.mm"
include "reximi.mm"
include "syl.mm"
include "ralrimiva.mm"
include "iunss2.mm"
include "wb.mm"
include "uneq1.mm"
include "0un.mm"
include "eqtrd.mm"
include "foeq3.mm"
include "mpbid.mm"
include "unisn0.mm"
include "eqcomi.mm"
include "founiiun.mm"
include "eqtr2d.mm"
include "0ss.mm"
include "eqsstrd.mm"
include "wn.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "simpr.mm"
include "elunnel1.mm"
include "elsni.mm"
include "adantllr.mm"
include "wex.mm"
include "neq0.mm"
include "biimpi.mm"
include "wi.mm"
include "id.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "ad4ant24.mm"
include "pm2.61dan.mm"
include "eqssd.mm"

theorem founiiun0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  assert |- ( F : A -onto-> ( B u. { (/) } ) -> U. B = U_ x e. A ( F ` x ) )

  proof
    cA
    cB
    c0
    csn
    #
    cun
    #
    cF
    wfo
    #
    cB
    cuni
    #
    vy
    cB
    vy
    cv
    #
    ciun
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    ciun
    #
    @3
    @5
    wceq
    @2
    vy
    cB
    uniiun
    a1i
    @2
    @5
    @8
    @2
    @4
    @7
    wss
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    @5
    @8
    wss
    @2
    @10
    vy
    cB
    @2
    @4
    cB
    wcel
    #
    wa
    #
    @7
    @4
    wceq
    #
    vx
    cA
    wrex
    #
    @10
    @12
    @2
    @4
    @1
    wcel
    #
    @14
    @2
    @11
    simpl
    @11
    @15
    @2
    @4
    cB
    @0
    elun1
    adantl
    vx
    cA
    @1
    cF
    @4
    foelrni
    syl2anc
    @13
    @9
    vx
    cA
    @4
    @7
    eqimss2
    reximi
    syl
    ralrimiva
    vy
    vx
    cB
    cA
    @4
    @7
    iunss2
    syl
    @2
    cB
    c0
    wceq
    #
    @8
    @5
    wss
    #
    @2
    @16
    wa
    #
    cA
    @0
    cF
    wfo
    #
    @17
    @18
    @2
    @19
    @2
    @16
    simpl
    @18
    @1
    @0
    wceq
    #
    @2
    @19
    wb
    @16
    @20
    @2
    @16
    @1
    c0
    @0
    cun
    #
    @0
    cB
    c0
    @0
    uneq1
    @21
    @0
    wceq
    @16
    @0
    0un
    a1i
    eqtrd
    adantl
    @1
    @0
    cA
    cF
    foeq3
    syl
    mpbid
    @19
    @8
    c0
    @5
    @19
    c0
    @0
    cuni
    #
    @8
    c0
    @22
    wceq
    @19
    @22
    c0
    unisn0
    eqcomi
    a1i
    vx
    cA
    @0
    cF
    founiiun
    eqtr2d
    c0
    @5
    wss
    @19
    @5
    0ss
    a1i
    eqsstrd
    syl
    @2
    @16
    wn
    #
    wa
    #
    @7
    @4
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    @17
    @24
    @26
    vx
    cA
    @24
    @6
    cA
    wcel
    #
    wa
    #
    @7
    cB
    wcel
    #
    @26
    @29
    @26
    @28
    @29
    @7
    @7
    wss
    #
    @26
    @7
    ssid
    @25
    @30
    vy
    @7
    cB
    @4
    @7
    @7
    sseq2
    rspcev
    mpan2
    adantl
    @28
    @29
    wn
    #
    wa
    @28
    @7
    c0
    wceq
    #
    @26
    @28
    @31
    simpl
    @2
    @27
    @31
    @32
    @23
    @2
    @27
    wa
    #
    @31
    wa
    #
    @7
    @0
    wcel
    #
    @32
    @34
    @7
    @1
    wcel
    #
    @31
    @35
    @33
    @36
    @31
    @2
    cA
    @1
    @6
    cF
    cA
    @1
    cF
    fof
    ffvelrnda
    adantr
    @33
    @31
    simpr
    @7
    cB
    @0
    elunnel1
    syl2anc
    @7
    c0
    elsni
    syl
    adantllr
    @23
    @32
    @26
    @2
    @27
    @23
    @32
    wa
    #
    @11
    @25
    wa
    #
    vy
    wex
    #
    @26
    @37
    @11
    vy
    wex
    #
    @39
    @23
    @40
    @32
    @23
    @40
    vy
    cB
    neq0
    biimpi
    adantr
    @37
    @11
    @38
    vy
    @32
    @11
    @38
    wi
    @23
    @32
    @11
    @38
    @32
    @11
    wa
    @11
    @25
    @32
    @11
    simpr
    @32
    @25
    @11
    @32
    @7
    c0
    @4
    @32
    id
    c0
    @4
    wss
    @32
    @4
    0ss
    a1i
    eqsstrd
    adantr
    jca
    ex
    adantl
    eximdv
    mpd
    @25
    vy
    cB
    df-rex
    sylibr
    ad4ant24
    syl2anc
    pm2.61dan
    ralrimiva
    vx
    vy
    cA
    cB
    @7
    @4
    iunss2
    syl
    pm2.61dan
    eqssd
    eqtrd
end
