include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "c-bnj18.mm"
include "wss.mm"
include "biimpri.mm"
include "cvv.mm"
include "w-bnj19.mm"
include "c-bnj14.mm"
include "bnj1413.mm"
include "cv.mm"
include "wral.mm"
include "ciun.mm"
include "simplll.mm"
include "bnj213.mm"
include "sseli.mm"
include "adantl.mm"
include "bnj906.mm"
include "syl2anc.mm"
include "bnj1318.mm"
include "ssiun2s.mm"
include "cun.mm"
include "ssun4.mm"
include "syl6sseqr.mm"
include "syl.mm"
include "sstrd.mm"
include "w3a.mm"
include "simpr.mm"
include "bnj1405.mm"
include "biid.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfun.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfan.mm"
include "nf5ri.mm"
include "bnj1521.mm"
include "3ad2ant1.mm"
include "bnj1147.mm"
include "simp3.mm"
include "bnj1213.mm"
include "simp2.mm"
include "bnj1125.mm"
include "syl3anc.mm"
include "ssiun2.mm"
include "3ad2ant2.mm"
include "bnj593.mm"
include "nfss.mm"
include "bnj1397.mm"
include "wo.mm"
include "bnj1138.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "df-bnj19.mm"
include "sylibr.mm"
include "bnj931.mm"
include "a1i.mm"
include "syl3anbrc.mm"
include "bnj1124.mm"
include "iunss1.mm"
include "unss2.mm"
include "3syl.mm"
include "3sstr4g.mm"
include "bnj1136.mm"
include "sseqtr4d.mm"
include "eqssd.mm"

theorem bnj1408
  let wth: wff th
  let wta: wff ta
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vz: setvar z
  assume bnj1408.1: |- B = ( _pred ( X , A , R ) u. U_ y e. _pred ( X , A , R ) _trCl ( y , A , R ) )
  assume bnj1408.2: |- C = ( _pred ( X , A , R ) u. U_ y e. _trCl ( X , A , R ) _trCl ( y , A , R ) )
  assume bnj1408.3: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1408.4: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint R z
  disjoint X z
  assert |- ( ( R _FrSe A /\ X e. A ) -> _trCl ( X , A , R ) = B )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    cA
    cR
    cX
    c-bnj18
    #
    cB
    @2
    wth
    wta
    @3
    cB
    wss
    wth
    @2
    bnj1408.3
    biimpri
    @2
    cB
    cvv
    wcel
    cA
    cB
    cR
    w-bnj19
    #
    cA
    cR
    cX
    c-bnj14
    #
    cB
    wss
    #
    wta
    vy
    cA
    cB
    cR
    cX
    bnj1408.1
    bnj1413
    @2
    cA
    cR
    vz
    cv
    #
    c-bnj14
    #
    cB
    wss
    #
    vz
    cB
    wral
    @4
    @2
    @9
    vz
    cB
    @2
    @7
    cB
    wcel
    #
    wa
    #
    @7
    @5
    wcel
    #
    @9
    @7
    vy
    @5
    cA
    cR
    vy
    cv
    #
    c-bnj18
    #
    ciun
    #
    wcel
    #
    @11
    @12
    wa
    #
    @8
    cA
    cR
    @7
    c-bnj18
    #
    cB
    @17
    @0
    @7
    cA
    wcel
    #
    @8
    @18
    wss
    #
    @0
    @1
    @10
    @12
    simplll
    @12
    @19
    @11
    @5
    cA
    @7
    cA
    cR
    cX
    bnj213
    #
    sseli
    adantl
    cA
    cR
    @7
    bnj906
    #
    syl2anc
    @12
    @18
    cB
    wss
    #
    @11
    @12
    @18
    @15
    wss
    #
    @23
    vy
    @5
    @14
    @7
    @18
    cA
    cR
    @13
    @7
    bnj1318
    ssiun2s
    @24
    @18
    @5
    @15
    cun
    #
    cB
    @18
    @15
    @5
    ssun4
    bnj1408.1
    syl6sseqr
    syl
    adantl
    sstrd
    @11
    @16
    wa
    #
    @9
    vy
    @26
    @26
    @13
    @5
    wcel
    #
    @7
    @14
    wcel
    #
    w3a
    #
    @9
    vy
    @28
    @26
    @29
    vy
    @5
    @26
    vy
    @5
    @14
    @7
    @11
    @16
    simpr
    bnj1405
    @29
    biid
    @26
    vy
    @11
    @16
    vy
    @2
    @10
    vy
    @2
    vy
    nfv
    vy
    vz
    cB
    vy
    cB
    @25
    bnj1408.1
    vy
    @5
    @15
    vy
    @5
    nfcv
    vy
    @5
    @14
    nfiu1
    #
    nfun
    nfcxfr
    #
    nfcri
    nfan
    vy
    vz
    @15
    @30
    nfcri
    nfan
    nf5ri
    bnj1521
    @29
    @8
    @14
    cB
    @29
    @8
    @18
    @14
    @29
    @0
    @19
    @20
    @26
    @27
    @0
    @28
    @0
    @1
    @10
    @16
    simplll
    3ad2ant1
    #
    @29
    vz
    @14
    cA
    cA
    cR
    @13
    bnj1147
    @26
    @27
    @28
    simp3
    #
    bnj1213
    @22
    syl2anc
    @29
    @0
    @13
    cA
    wcel
    @28
    @18
    @14
    wss
    @32
    @29
    vy
    @5
    cA
    @21
    @26
    @27
    @28
    simp2
    bnj1213
    @33
    cA
    cR
    @13
    @7
    bnj1125
    syl3anc
    sstrd
    @29
    @14
    @15
    wss
    #
    @14
    cB
    wss
    @27
    @26
    @34
    @28
    vy
    @5
    @14
    ssiun2
    3ad2ant2
    @34
    @14
    @25
    cB
    @14
    @15
    @5
    ssun4
    bnj1408.1
    syl6sseqr
    syl
    sstrd
    bnj593
    @9
    vy
    vy
    @8
    cB
    vy
    @8
    nfcv
    @31
    nfss
    nf5ri
    bnj1397
    @11
    @10
    @12
    @16
    wo
    @2
    @10
    simpr
    cB
    @5
    @15
    @7
    bnj1408.1
    bnj1138
    sylib
    mpjaodan
    ralrimiva
    vz
    cA
    cB
    cR
    df-bnj19
    sylibr
    @6
    @2
    cB
    @5
    @15
    bnj1408.1
    bnj931
    a1i
    bnj1408.4
    syl3anbrc
    wth
    wta
    cA
    cB
    cR
    cX
    bnj1408.3
    bnj1408.4
    bnj1124
    syl2anc
    @2
    cB
    cC
    @3
    @2
    @25
    @5
    vy
    @3
    @14
    ciun
    #
    cun
    #
    cB
    cC
    @2
    @5
    @3
    wss
    @15
    @35
    wss
    @25
    @36
    wss
    cA
    cR
    cX
    bnj906
    vy
    @5
    @3
    @14
    iunss1
    @15
    @35
    @5
    unss2
    3syl
    bnj1408.1
    bnj1408.2
    3sstr4g
    @2
    cC
    cvv
    wcel
    cA
    cC
    cR
    w-bnj19
    @5
    cC
    wss
    w3a
    #
    vy
    cA
    cC
    cR
    cX
    bnj1408.2
    @2
    biid
    @37
    biid
    bnj1136
    sseqtr4d
    eqssd
end
