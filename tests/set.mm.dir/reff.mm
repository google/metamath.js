include "wcel.mm"
include "cref.mm"
include "wbr.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "ssid.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "isref.mm"
include "simprbda.mm"
include "syl5sseq.mm"
include "simplbda.mm"
include "wi.mm"
include "sseq2.mm"
include "ac6sg.mm"
include "adantr.mm"
include "mpd.mm"
include "jca.mm"
include "simplr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simplrl.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "simplrr.mm"
include "rspa.mm"
include "syl2anc.mm"
include "sselda.mm"
include "eleq2.mm"
include "rspcev.mm"
include "eluni2.mm"
include "sylib.mm"
include "r19.29af.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ralrimi.mm"
include "wb.mm"
include "ad2antrr.mm"
include "mpbir2and.mm"
include "exlimdv.mm"
include "impr.mm"
include "impbida.mm"

theorem reff
  let vv: setvar v
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let vx: setvar x
  let vu: setvar u

  disjoint A f
  disjoint A v
  disjoint f v
  disjoint B f
  disjoint B v
  disjoint V f
  disjoint V v
  disjoint A x
  disjoint f x
  disjoint v x
  disjoint B u
  disjoint B x
  disjoint f u
  disjoint u v
  disjoint u x
  disjoint V x
  assert |- ( A e. V -> ( A Ref B <-> ( U. B C_ U. A /\ E. f ( f : A --> B /\ A. v e. A v C_ ( f ` v ) ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cref
    wbr
    #
    cB
    cuni
    #
    cA
    cuni
    #
    wss
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    vv
    cv
    #
    @7
    @5
    cfv
    #
    wss
    #
    vv
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    wa
    @0
    @1
    wa
    #
    @4
    @12
    @13
    @2
    @2
    @3
    @2
    ssid
    @0
    @1
    @2
    @3
    wceq
    #
    @7
    vu
    cv
    #
    wss
    #
    vu
    cB
    wrex
    #
    vv
    cA
    wral
    #
    vv
    vu
    cA
    cB
    cV
    @3
    @2
    @3
    eqid
    @2
    eqid
    isref
    #
    simprbda
    syl5sseq
    @13
    @18
    @12
    @0
    @1
    @14
    @18
    @19
    simplbda
    @0
    @18
    @12
    wi
    @1
    @16
    @9
    vv
    vu
    cA
    cB
    vf
    cV
    @15
    @8
    @7
    sseq2
    #
    ac6sg
    adantr
    mpd
    jca
    @0
    @4
    @12
    @1
    @0
    @4
    wa
    #
    @11
    @1
    vf
    @21
    @11
    @1
    @21
    @11
    wa
    #
    @1
    @14
    @18
    @22
    @2
    @3
    @0
    @4
    @11
    simplr
    @22
    vx
    @3
    @2
    @22
    vx
    cv
    #
    @3
    wcel
    #
    @23
    @2
    wcel
    #
    @22
    @24
    wa
    #
    @23
    @15
    wcel
    #
    vu
    cB
    wrex
    #
    @25
    @26
    @23
    @7
    wcel
    #
    @28
    vv
    cA
    @22
    @24
    vv
    @21
    @11
    vv
    @21
    vv
    nfv
    @6
    @10
    vv
    @6
    vv
    nfv
    @9
    vv
    cA
    nfra1
    nfan
    nfan
    #
    @24
    vv
    nfv
    nfan
    @26
    @7
    cA
    wcel
    #
    wa
    #
    @29
    wa
    @8
    cB
    wcel
    #
    @23
    @8
    wcel
    #
    @28
    @32
    @33
    @29
    @22
    @31
    @33
    @24
    @22
    @31
    wa
    #
    cA
    cB
    @7
    @5
    @21
    @6
    @10
    @31
    simplrl
    @22
    @31
    simpr
    #
    ffvelrnd
    #
    adantlr
    adantr
    @32
    @7
    @8
    @23
    @32
    @10
    @31
    @9
    @22
    @31
    @10
    @24
    @21
    @6
    @10
    @31
    simplrr
    #
    adantlr
    @26
    @31
    simpr
    @9
    vv
    cA
    rspa
    #
    syl2anc
    sselda
    @27
    @34
    vu
    @8
    cB
    @15
    @8
    @23
    eleq2
    rspcev
    syl2anc
    @26
    @24
    @29
    vv
    cA
    wrex
    @22
    @24
    simpr
    vv
    @23
    cA
    eluni2
    sylib
    r19.29af
    vu
    @23
    cB
    eluni2
    sylibr
    ex
    ssrdv
    eqssd
    @22
    @17
    vv
    cA
    @30
    @22
    @31
    @17
    @35
    @33
    @9
    @17
    @37
    @35
    @10
    @31
    @9
    @38
    @36
    @39
    syl2anc
    @16
    @9
    vu
    @8
    cB
    @20
    rspcev
    syl2anc
    ex
    ralrimi
    @0
    @1
    @14
    @18
    wa
    wb
    @4
    @11
    @19
    ad2antrr
    mpbir2and
    ex
    exlimdv
    impr
    impbida
end
