include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "ccgr.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "orbi1d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "wne.mm"
include "simp1.mm"
include "simp2.mm"
include "ancomd.mm"
include "axsegcon.mm"
include "syl3anc.mm"
include "adantr.mm"
include "wi.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2l.mm"
include "simpl3.mm"
include "syl121anc.mm"
include "anass.mm"
include "df-3an.mm"
include "simpr1.mm"
include "wb.mm"
include "simpr2r.mm"
include "simprl.mm"
include "simpl2r.mm"
include "cgrdegen.mm"
include "syl122anc.mm"
include "mpd.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "necomd.mm"
include "simpr2l.mm"
include "btwncomand.mm"
include "simpr3.mm"
include "simprr.mm"
include "btwnconn2.mm"
include "mp3and.mm"
include "sylan2br.mm"
include "expr.mm"
include "anim1d.mm"
include "sylanb.mm"
include "an32s.mm"
include "reximdva.mm"
include "rexlimdva.mm"
include "simp2l.mm"
include "simp3.mm"
include "orc.mm"
include "anim1i.mm"
include "reximi.mm"
include "syl.mm"
include "pm2.61ne.mm"

theorem segcon2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cN: class N
  let va: setvar a

  disjoint Q x
  disjoint N x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint Q a
  disjoint a x
  disjoint N a
  disjoint A a
  disjoint B a
  disjoint C a
  assert |- ( ( N e. NN /\ ( Q e. ( EE ` N ) /\ A e. ( EE ` N ) ) /\ ( B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> E. x e. ( EE ` N ) ( ( A Btwn <. Q , x >. \/ x Btwn <. Q , A >. ) /\ <. Q , x >. Cgr <. B , C >. ) )

  proof
    cN
    cn
    wcel
    #
    cQ
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
    wa
    #
    cB
    @1
    wcel
    cC
    @1
    wcel
    wa
    #
    w3a
    #
    cA
    cQ
    vx
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @7
    cQ
    cA
    cop
    cbtwn
    wbr
    #
    wo
    #
    @8
    cB
    cC
    cop
    ccgr
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    cQ
    @8
    cbtwn
    wbr
    #
    @10
    wo
    #
    @12
    wa
    #
    vx
    @1
    wrex
    #
    cA
    cQ
    cA
    cQ
    wceq
    #
    @13
    @17
    vx
    @1
    @19
    @11
    @16
    @12
    @19
    @9
    @15
    @10
    cA
    cQ
    @8
    cbtwn
    breq1
    orbi1d
    anbi1d
    rexbidv
    @6
    cA
    cQ
    wne
    #
    wa
    #
    cQ
    cA
    va
    cv
    #
    cop
    cbtwn
    wbr
    #
    cQ
    @22
    cop
    cA
    cQ
    cop
    ccgr
    wbr
    #
    wa
    #
    va
    @1
    wrex
    #
    @14
    @6
    @26
    @20
    @6
    @0
    @3
    @2
    wa
    #
    @27
    @26
    @0
    @4
    @5
    simp1
    #
    @6
    @2
    @3
    @0
    @4
    @5
    simp2
    ancomd
    #
    @29
    va
    cA
    cQ
    cA
    cQ
    cN
    axsegcon
    syl3anc
    adantr
    @21
    @25
    @14
    va
    @1
    @6
    @22
    @1
    wcel
    #
    @20
    @25
    @14
    wi
    @6
    @30
    wa
    #
    @20
    @25
    @14
    @31
    @20
    @25
    wa
    #
    wa
    #
    cQ
    @22
    @7
    cop
    cbtwn
    wbr
    #
    @12
    wa
    #
    vx
    @1
    wrex
    #
    @14
    @31
    @36
    @32
    @31
    @0
    @30
    @2
    @5
    @36
    @0
    @4
    @5
    @30
    simpl1
    @6
    @30
    simpr
    @2
    @3
    @0
    @5
    @30
    simpl2l
    @0
    @4
    @5
    @30
    simpl3
    vx
    @22
    cQ
    cB
    cC
    cN
    axsegcon
    syl121anc
    adantr
    @33
    @35
    @13
    vx
    @1
    @31
    @7
    @1
    wcel
    #
    @32
    @35
    @13
    wi
    #
    @31
    @37
    wa
    @6
    @30
    @37
    wa
    #
    wa
    #
    @32
    @38
    @6
    @30
    @37
    anass
    @40
    @32
    wa
    @34
    @11
    @12
    @40
    @32
    @34
    @11
    @32
    @34
    wa
    @40
    @20
    @25
    @34
    w3a
    #
    @11
    @20
    @25
    @34
    df-3an
    @40
    @41
    wa
    #
    @22
    cQ
    wne
    #
    cQ
    @22
    cA
    cop
    cbtwn
    wbr
    #
    @34
    @11
    @42
    cQ
    @22
    @42
    cQ
    @22
    wne
    @20
    @40
    @20
    @25
    @34
    simpr1
    @42
    cQ
    @22
    cA
    cQ
    @42
    @24
    cQ
    @22
    wceq
    @19
    wb
    #
    @23
    @24
    @20
    @34
    @40
    simpr2r
    @40
    @24
    @45
    wi
    #
    @41
    @40
    @0
    @2
    @30
    @3
    @2
    @46
    @0
    @4
    @5
    @39
    simpl1
    #
    @2
    @3
    @0
    @5
    @39
    simpl2l
    #
    @6
    @30
    @37
    simprl
    #
    @2
    @3
    @0
    @5
    @39
    simpl2r
    #
    @48
    cQ
    @22
    cA
    cQ
    cN
    cgrdegen
    syl122anc
    adantr
    mpd
    necon3bid
    mpbird
    necomd
    @40
    @41
    cQ
    cA
    @22
    cN
    @47
    @48
    @50
    @49
    @23
    @24
    @20
    @34
    @40
    simpr2l
    btwncomand
    @40
    @20
    @25
    @34
    simpr3
    @40
    @43
    @44
    @34
    w3a
    @11
    wi
    #
    @41
    @40
    @0
    @30
    @2
    @3
    @37
    @51
    @47
    @49
    @48
    @50
    @6
    @30
    @37
    simprr
    @22
    cQ
    cA
    @7
    cN
    btwnconn2
    syl122anc
    adantr
    mp3and
    sylan2br
    expr
    anim1d
    sylanb
    an32s
    reximdva
    mpd
    expr
    an32s
    rexlimdva
    mpd
    @6
    @15
    @12
    wa
    #
    vx
    @1
    wrex
    #
    @18
    @6
    @0
    @2
    @2
    @5
    @53
    @28
    @0
    @2
    @3
    @5
    simp2l
    #
    @54
    @0
    @4
    @5
    simp3
    vx
    cQ
    cQ
    cB
    cC
    cN
    axsegcon
    syl121anc
    @52
    @17
    vx
    @1
    @15
    @16
    @12
    @15
    @10
    orc
    anim1i
    reximi
    syl
    pm2.61ne
end
