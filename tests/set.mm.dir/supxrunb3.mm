include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2re.mm"
include "adantl.mm"
include "simpl.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "adantll.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfral.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "simp1r.mm"
include "rexr.mm"
include "syl.mm"
include "rexrd.mm"
include "simp1l.mm"
include "simp2.mm"
include "ssel2.mm"
include "ltp1d.mm"
include "simp3.mm"
include "xrltletrd.mm"
include "3exp.mm"
include "adantlr.mm"
include "reximdai.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "nfra1.mm"
include "simpll.mm"
include "simpr.mm"
include "rspa.mm"
include "ad3antlr.mm"
include "adantr.mm"
include "adantllr.mm"
include "xrltled.mm"
include "reximdva.mm"
include "syl21anc.mm"
include "ralrimi.mm"
include "sylan2.mm"
include "impbid.mm"
include "supxrunb2.mm"
include "bitrd.mm"

theorem supxrunb3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A w
  disjoint w x
  disjoint w y
  assert |- ( A C_ RR* -> ( A. x e. RR E. y e. A x <_ y <-> sup ( A , RR* , < ) = +oo ) )

  proof
    cA
    cxr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    #
    vw
    cv
    #
    @2
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vw
    cr
    wral
    #
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    @0
    @5
    @9
    @0
    @5
    @9
    @0
    @5
    wa
    #
    @8
    vw
    cr
    @10
    @6
    cr
    wcel
    #
    wa
    #
    @6
    c1
    caddc
    co
    #
    @2
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    @8
    @5
    @11
    @15
    @0
    @5
    @11
    wa
    @13
    cr
    wcel
    #
    @5
    @15
    @11
    @16
    @5
    @6
    peano2re
    #
    adantl
    @5
    @11
    simpl
    @4
    @15
    vx
    @13
    cr
    @1
    @13
    wceq
    @3
    @14
    vy
    cA
    @1
    @13
    @2
    cle
    breq1
    rexbidv
    rspcva
    syl2anc
    adantll
    @12
    @14
    @7
    vy
    cA
    @10
    @11
    vy
    @0
    @5
    vy
    @0
    vy
    nfv
    @4
    vy
    vx
    cr
    vy
    cr
    nfcv
    @3
    vy
    cA
    nfre1
    nfral
    nfan
    @11
    vy
    nfv
    nfan
    @0
    @11
    @2
    cA
    wcel
    #
    @14
    @7
    wi
    wi
    @5
    @0
    @11
    wa
    #
    @18
    @14
    @7
    @19
    @18
    @14
    w3a
    #
    @6
    @13
    @2
    @20
    @11
    @6
    cxr
    wcel
    @0
    @11
    @18
    @14
    simp1r
    #
    @6
    rexr
    syl
    @20
    @11
    @13
    cxr
    wcel
    @21
    @11
    @13
    @17
    rexrd
    syl
    @20
    @0
    @18
    @2
    cxr
    wcel
    #
    @0
    @11
    @18
    @14
    simp1l
    @19
    @18
    @14
    simp2
    cA
    cxr
    @2
    ssel2
    #
    syl2anc
    @20
    @6
    @21
    ltp1d
    @19
    @18
    @14
    simp3
    xrltletrd
    3exp
    adantlr
    reximdai
    mpd
    ralrimiva
    ex
    @0
    @9
    @5
    @9
    @0
    @1
    @2
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    #
    @5
    @9
    @26
    @8
    @25
    vw
    vx
    cr
    @6
    @1
    wceq
    @7
    @24
    vy
    cA
    @6
    @1
    @2
    clt
    breq1
    rexbidv
    cbvralv
    biimpi
    @0
    @26
    wa
    #
    @4
    vx
    cr
    @0
    @26
    vx
    @0
    vx
    nfv
    @25
    vx
    cr
    nfra1
    nfan
    @27
    @1
    cr
    wcel
    #
    @4
    @27
    @28
    wa
    #
    @0
    @28
    @4
    @4
    @0
    @26
    @28
    simpll
    @27
    @28
    simpr
    @29
    @25
    @4
    @26
    @28
    @25
    @0
    @25
    vx
    cr
    rspa
    adantll
    @0
    @28
    @25
    @4
    wi
    @26
    @0
    @28
    wa
    #
    @24
    @3
    vy
    cA
    @30
    @18
    wa
    #
    @24
    @3
    @31
    @24
    wa
    @1
    @2
    @28
    @1
    cxr
    wcel
    @0
    @18
    @24
    @1
    rexr
    ad3antlr
    @0
    @18
    @24
    @22
    @28
    @0
    @18
    wa
    @22
    @24
    @23
    adantr
    adantllr
    @31
    @24
    simpr
    xrltled
    ex
    reximdva
    adantlr
    mpd
    @30
    @4
    simpr
    syl21anc
    ex
    ralrimi
    sylan2
    ex
    impbid
    vw
    vy
    cA
    supxrunb2
    bitrd
end
