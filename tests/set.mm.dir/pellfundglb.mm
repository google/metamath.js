include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cr.mm"
include "cpellfund.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wn.mm"
include "c1.mm"
include "cpell14qr.mm"
include "crab.mm"
include "wrex.mm"
include "wa.mm"
include "cpell1qr.mm"
include "wral.mm"
include "cinf.mm"
include "wceq.mm"
include "pellfundval.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "eqbrtrrd.mm"
include "pellfundre.mm"
include "eqeltrrd.mm"
include "simp2.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "ssrab2.mm"
include "pell14qrre.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl5ss.mm"
include "pell1qrss14.mm"
include "pellqrex.mm"
include "ssrexv.mm"
include "sylc.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infmrgelbi.mm"
include "syl3anc.mm"
include "mtod.mm"
include "rexnal.mm"
include "breq2.mm"
include "elrab.mm"
include "simprl.mm"
include "1red.mm"
include "simpl1.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ltled.mm"
include "jca.mm"
include "wb.mm"
include "elpell1qr2.mm"
include "syl.mm"
include "mpbird.mm"
include "sylan2b.mm"
include "adantrr.mm"
include "sseldi.mm"
include "simpr.mm"
include "a1i.mm"
include "syl5bi.mm"
include "imp.mm"
include "pellfundlb.mm"
include "adantr.mm"
include "sseldd.mm"
include "simpl2.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem pellfundglb
  let vx: setvar x
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint D x
  disjoint A x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint A d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  assert |- ( ( D e. ( NN \ []NN ) /\ A e. RR /\ ( PellFund ` D ) < A ) -> E. x e. ( Pell1QR ` D ) ( ( PellFund ` D ) <_ x /\ x < A ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cr
    wcel
    #
    cD
    cpellfund
    cfv
    #
    cA
    clt
    wbr
    #
    w3a
    #
    cA
    vx
    cv
    #
    cle
    wbr
    #
    wn
    #
    vx
    c1
    va
    cv
    #
    clt
    wbr
    #
    va
    cD
    cpell14qr
    cfv
    #
    crab
    #
    wrex
    #
    @2
    @5
    cle
    wbr
    #
    @5
    cA
    clt
    wbr
    #
    wa
    #
    vx
    cD
    cpell1qr
    cfv
    #
    wrex
    @4
    @6
    vx
    @11
    wral
    #
    wn
    @12
    @4
    @17
    cA
    @11
    cr
    clt
    cinf
    #
    cle
    wbr
    #
    @4
    @18
    cA
    clt
    wbr
    @19
    wn
    @4
    @2
    @18
    cA
    clt
    @0
    @1
    @2
    @18
    wceq
    @3
    va
    cD
    pellfundval
    3ad2ant1
    #
    @0
    @1
    @3
    simp3
    eqbrtrrd
    @4
    @18
    cA
    @4
    @2
    @18
    cr
    @20
    @0
    @1
    @2
    cr
    wcel
    @3
    cD
    pellfundre
    3ad2ant1
    eqeltrrd
    @0
    @1
    @3
    simp2
    #
    ltnled
    mpbid
    @4
    @11
    cr
    wss
    #
    @11
    c0
    wne
    #
    @1
    @17
    @19
    wi
    @4
    @11
    @10
    cr
    @9
    va
    @10
    ssrab2
    #
    @0
    @1
    @10
    cr
    wss
    #
    @3
    @0
    va
    @10
    cr
    @0
    @8
    @10
    wcel
    @8
    cr
    wcel
    @8
    cD
    pell14qrre
    ex
    ssrdv
    3ad2ant1
    #
    syl5ss
    @4
    @9
    va
    @10
    wrex
    #
    @23
    @4
    @16
    @10
    wss
    #
    @9
    va
    @16
    wrex
    #
    @27
    @0
    @1
    @28
    @3
    cD
    pell1qrss14
    3ad2ant1
    @0
    @1
    @29
    @3
    va
    cD
    pellqrex
    3ad2ant1
    @9
    va
    @16
    @10
    ssrexv
    sylc
    @9
    va
    @10
    rabn0
    sylibr
    @21
    @22
    @23
    @1
    w3a
    @17
    @19
    vx
    @11
    cA
    infmrgelbi
    ex
    syl3anc
    mtod
    @6
    vx
    @11
    rexnal
    sylibr
    @4
    @7
    @15
    vx
    @11
    @16
    @4
    @5
    @11
    wcel
    #
    @7
    wa
    #
    @5
    @16
    wcel
    #
    @15
    wa
    @4
    @31
    wa
    #
    @32
    @15
    @4
    @30
    @32
    @7
    @30
    @4
    @5
    @10
    wcel
    #
    c1
    @5
    clt
    wbr
    #
    wa
    #
    @32
    @9
    @35
    va
    @5
    @10
    @8
    @5
    c1
    clt
    breq2
    elrab
    #
    @4
    @36
    wa
    #
    @32
    @34
    c1
    @5
    cle
    wbr
    #
    wa
    #
    @38
    @34
    @39
    @4
    @34
    @35
    simprl
    #
    @38
    c1
    @5
    @38
    1red
    @38
    @0
    @34
    @5
    cr
    wcel
    @0
    @1
    @3
    @36
    simpl1
    #
    @41
    @5
    cD
    pell14qrre
    syl2anc
    @4
    @34
    @35
    simprr
    ltled
    jca
    @38
    @0
    @32
    @40
    wb
    @42
    @5
    cD
    elpell1qr2
    syl
    mpbird
    sylan2b
    adantrr
    @33
    @13
    @14
    @33
    @0
    @34
    @35
    @13
    @0
    @1
    @3
    @31
    simpl1
    @33
    @11
    @10
    @5
    @24
    @4
    @30
    @7
    simprl
    sseldi
    #
    @4
    @30
    @35
    @7
    @4
    @30
    @35
    @30
    @36
    @4
    @35
    @37
    @36
    @35
    wi
    @4
    @34
    @35
    simpr
    a1i
    syl5bi
    imp
    adantrr
    @5
    cD
    pellfundlb
    syl3anc
    @33
    @14
    @7
    @4
    @30
    @7
    simprr
    @33
    @5
    cA
    @33
    @10
    cr
    @5
    @4
    @25
    @31
    @26
    adantr
    @43
    sseldd
    @0
    @1
    @3
    @31
    simpl2
    ltnled
    mpbird
    jca
    jca
    ex
    reximdv2
    mpd
end
