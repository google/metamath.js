include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "wne.mm"
include "cbtwn.mm"
include "wo.mm"
include "cv.mm"
include "wrex.mm"
include "broutsideof2.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr1.mm"
include "btwndiff.mm"
include "syl3anc.mm"
include "adantr.mm"
include "wi.mm"
include "df-3an.mm"
include "3anass.mm"
include "necomd.mm"
include "simp1.mm"
include "simp23.mm"
include "simp22.mm"
include "simp21.mm"
include "simp3.mm"
include "simpr1r.mm"
include "btwncomand.mm"
include "simpr2.mm"
include "btwnexch3and.mm"
include "3jca.mm"
include "syl2anbr.mm"
include "expr.mm"
include "an32s.mm"
include "reximdva.mm"
include "mpd.mm"
include "jaod.mm"
include "simprr1.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "simprr2.mm"
include "simplr3.mm"
include "simprr3.mm"
include "btwnconn2.mm"
include "syl122anc.mm"
include "mp3and.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem broutsideof3
  let cA: class A
  let cB: class B
  let cP: class P
  let cN: class N
  let vc: setvar c

  disjoint N c
  disjoint A c
  disjoint B c
  disjoint P c
  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) -> ( P OutsideOf <. A , B >. <-> ( A =/= P /\ B =/= P /\ E. c e. ( EE ` N ) ( c =/= P /\ P Btwn <. A , c >. /\ P Btwn <. B , c >. ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cA
    @1
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cP
    cA
    cB
    cop
    coutsideof
    wbr
    cA
    cP
    wne
    #
    cB
    cP
    wne
    #
    cA
    cP
    cB
    cop
    cbtwn
    wbr
    #
    cB
    cP
    cA
    cop
    cbtwn
    wbr
    #
    wo
    #
    w3a
    #
    @7
    @8
    vc
    cv
    #
    cP
    wne
    #
    cP
    cA
    @13
    cop
    cbtwn
    wbr
    #
    cP
    cB
    @13
    cop
    cbtwn
    wbr
    #
    w3a
    #
    vc
    @1
    wrex
    #
    w3a
    #
    cA
    cB
    cP
    cN
    broutsideof2
    @6
    @7
    @8
    wa
    #
    @11
    wa
    @20
    @18
    wa
    @12
    @19
    @6
    @20
    @11
    @18
    @6
    @20
    wa
    #
    @11
    @18
    @21
    @9
    @18
    @10
    @6
    @20
    @9
    @18
    @6
    @20
    @9
    wa
    #
    wa
    #
    @16
    cP
    @13
    wne
    #
    wa
    #
    vc
    @1
    wrex
    #
    @18
    @6
    @26
    @22
    @6
    @0
    @4
    @2
    @26
    @0
    @5
    simpl
    #
    @0
    @2
    @3
    @4
    simpr3
    @0
    @2
    @3
    @4
    simpr1
    #
    cB
    cP
    cN
    vc
    btwndiff
    syl3anc
    adantr
    @23
    @25
    @17
    vc
    @1
    @6
    @13
    @1
    wcel
    #
    @22
    @25
    @17
    wi
    @6
    @29
    wa
    #
    @22
    @25
    @17
    @30
    @0
    @5
    @29
    w3a
    #
    @22
    @16
    @24
    w3a
    #
    @17
    @22
    @25
    wa
    @0
    @5
    @29
    df-3an
    #
    @22
    @16
    @24
    3anass
    @31
    @32
    wa
    #
    @14
    @15
    @16
    @34
    cP
    @13
    @31
    @22
    @16
    @24
    simpr3
    necomd
    @31
    @32
    cB
    cA
    cP
    @13
    cN
    @0
    @5
    @29
    simp1
    #
    @0
    @2
    @3
    @4
    @29
    simp23
    #
    @0
    @2
    @3
    @4
    @29
    simp22
    #
    @0
    @2
    @3
    @4
    @29
    simp21
    #
    @0
    @5
    @29
    simp3
    #
    @31
    @32
    cA
    cP
    cB
    cN
    @35
    @37
    @38
    @36
    @20
    @9
    @16
    @24
    @31
    simpr1r
    btwncomand
    @31
    @22
    @16
    @24
    simpr2
    #
    btwnexch3and
    @40
    3jca
    syl2anbr
    expr
    an32s
    reximdva
    mpd
    expr
    @6
    @20
    @10
    @18
    @6
    @20
    @10
    wa
    #
    wa
    #
    @15
    @24
    wa
    #
    vc
    @1
    wrex
    #
    @18
    @6
    @44
    @41
    @6
    @0
    @3
    @2
    @44
    @27
    @0
    @2
    @3
    @4
    simpr2
    @28
    cA
    cP
    cN
    vc
    btwndiff
    syl3anc
    adantr
    @42
    @43
    @17
    vc
    @1
    @6
    @29
    @41
    @43
    @17
    wi
    @30
    @41
    @43
    @17
    @30
    @31
    @41
    @15
    @24
    w3a
    #
    @17
    @41
    @43
    wa
    @33
    @41
    @15
    @24
    3anass
    @31
    @45
    wa
    #
    @14
    @15
    @16
    @46
    cP
    @13
    @31
    @41
    @15
    @24
    simpr3
    necomd
    @31
    @41
    @15
    @24
    simpr2
    #
    @31
    @45
    cA
    cB
    cP
    @13
    cN
    @35
    @37
    @36
    @38
    @39
    @31
    @45
    cB
    cP
    cA
    cN
    @35
    @36
    @38
    @37
    @20
    @10
    @15
    @24
    @31
    simpr1r
    btwncomand
    @47
    btwnexch3and
    3jca
    syl2anbr
    expr
    an32s
    reximdva
    mpd
    expr
    jaod
    @21
    @17
    @11
    vc
    @1
    @6
    @29
    @20
    @17
    @11
    wi
    @30
    @20
    @17
    @11
    @30
    @20
    @17
    wa
    #
    wa
    @14
    cP
    @13
    cA
    cop
    cbtwn
    wbr
    #
    cP
    @13
    cB
    cop
    cbtwn
    wbr
    #
    @11
    @14
    @15
    @16
    @20
    @30
    simprr1
    @30
    @48
    cP
    cA
    @13
    cN
    @0
    @5
    @29
    simpll
    #
    @2
    @3
    @4
    @0
    @29
    simplr1
    #
    @2
    @3
    @4
    @0
    @29
    simplr2
    #
    @6
    @29
    simpr
    #
    @14
    @15
    @16
    @20
    @30
    simprr2
    btwncomand
    @30
    @48
    cP
    cB
    @13
    cN
    @51
    @52
    @2
    @3
    @4
    @0
    @29
    simplr3
    #
    @54
    @14
    @15
    @16
    @20
    @30
    simprr3
    btwncomand
    @30
    @14
    @49
    @50
    w3a
    @11
    wi
    #
    @48
    @30
    @0
    @29
    @2
    @3
    @4
    @56
    @51
    @54
    @52
    @53
    @55
    @13
    cP
    cA
    cB
    cN
    btwnconn2
    syl122anc
    adantr
    mp3and
    expr
    an32s
    rexlimdva
    impbid
    pm5.32da
    @7
    @8
    @11
    df-3an
    @7
    @8
    @18
    df-3an
    3bitr4g
    bitrd
end
